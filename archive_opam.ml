let reason_field = "x-reason-for-archiving"

let commit_field = "x-opam-repository-commit-hash-at-time-of-archiving"

type reason =
  | OCaml_version
  | Source_unavailable
  | Maintenance_intent
  | Uninstallable

let reason_to_string = function
  | OCaml_version -> "ocaml-version"
  | Source_unavailable -> "source-unavailable"
  | Maintenance_intent -> "maintenance-intent"
  | Uninstallable -> "uninstallable"

let reason_of_string = function
  | "ocaml-version" -> Ok OCaml_version
  | "source-unavailable" -> Ok Source_unavailable
  | "maintenance-intent" -> Ok Maintenance_intent
  | "uninstallable" -> Ok Uninstallable
  | x -> Error (`Msg ("unknown reason: " ^ x))

let reason_enum = [
  "ocaml-version", OCaml_version ;
  "source-unavailable", Source_unavailable ;
  "maintenance-intent", Maintenance_intent ;
  "uninstallable", Uninstallable ;
]

module S = Set.Make(String)

let v_with_pos filename v =
  let pos = OpamParserTypes.FullPos.{ filename ; start = 0, 0 ; stop = 0, 0 } in
  OpamParserTypes.FullPos.{ pelem = v ; pos }

let pkg_name_and_version path =
  match List.rev (Fpath.segs path) with
  | _opam :: pkg_ver :: pkg :: _rest -> pkg, pkg_ver
  | _ -> assert false

let opam_archive commit reason deps fpath opam =
  let filename = Fpath.to_string fpath in
  let commit = v_with_pos filename (OpamParserTypes.FullPos.String commit) in
  let opam = OpamFile.OPAM.add_extension opam commit_field commit in
  let reason =
    let open OpamParserTypes.FullPos in
    let r = reason_to_string (reason fpath) in
    v_with_pos filename
      (List (v_with_pos filename ([ v_with_pos filename (String r) ] )))
  in
  let opam = OpamFile.OPAM.add_extension opam reason_field reason in
  OpamFile.OPAM.with_depends deps opam

let pp_pkg ppf fpath =
  let _, pkg_ver = pkg_name_and_version fpath in
  Fmt.string ppf pkg_ver

let pick_latest opams name =
  OpamPackage.Set.fold (fun pkg acc ->
      if OpamPackage.Name.equal pkg.OpamPackage.name name then
        match acc with
        | None, _ -> Some pkg, false
        | Some pkg', _ ->
          let str pkg = OpamPackage.to_string pkg in
          if OpamVersionCompare.compare (str pkg) (str pkg') <= 0 then
            Some pkg', true
          else
            Some pkg, true
      else
        acc) opams (None, false)

let string_of_relop = OpamPrinter.FullPos.relop_kind

let rec filter_to_string = function
  | OpamTypes.FBool b -> string_of_bool b
  | FString s -> "\"" ^ s ^ "\""
  | FIdent (_opt_names, var, _env) ->
    OpamVariable.to_string var
  | FOp (f, rel, g) ->
    filter_to_string f ^ " " ^ string_of_relop rel ^ " " ^ filter_to_string g
  | FAnd (f, g) ->
    filter_to_string f ^ " && " ^ filter_to_string g
  | FOr (f, g) ->
    filter_to_string f ^ " || " ^ filter_to_string g
  | FNot f -> "not " ^ filter_to_string f
  | FDefined f -> "defined " ^ filter_to_string f
  | FUndef f -> "undefined " ^ filter_to_string f

let f_to_string = function
  | OpamTypes.Filter filter -> filter_to_string filter
  | Constraint (relop, filter) ->
    string_of_relop relop ^ " " ^ filter_to_string filter

let rec condition_to_string = function
  | OpamTypes.Empty -> ""
  | Atom f -> f_to_string f
  | Block a -> condition_to_string a
  | And (a, b) -> condition_to_string a ^ " & " ^ condition_to_string b
  | Or (a, b) -> condition_to_string a ^ " | " ^ condition_to_string b

let adapt_deps no_upper_bound opams opam =
  let current_deps = OpamFile.OPAM.depends opam in
  let rec locked_deps = function
    | OpamFormula.Empty as a -> a
    | Atom (name, condition) ->
      if OpamPackage.Name.Set.mem name no_upper_bound then begin
        Atom (name, condition)
      end else begin
        match pick_latest opams name with
        | None, _ ->
          Logs.err (fun m -> m "couldn't find latest for %s"
                       (OpamPackage.Name.to_string name));
          Atom (name, condition)
        | Some { OpamPackage.version = highest ; _ }, multiple_versions ->
          (* this adds the <= highest constrain to the existing depends clause.
             now, we try to be smart:
             - if there's a {= X} constraint, we don't need to add anything
               (has_equal_constraint)
             - if there's a {< X} or {<= X} constraint where X is smaller or
               equal highest, we don't add anything (has_leq_lt_constraint)
             - if there's a {>= X} constraint where X = highest, we add {= X}
               (has_geq_constraint)

             Also, keep in mind that "multiple_versions" is true if there's only
             a single opam version. If this is the case, we use {= highest}
             instead.
          *)
          let h = OpamPackage.Version.to_string highest in
          let upper_bound, equal_bound =
            let op = if multiple_versions then `Leq else `Eq in
            let bound op = OpamTypes.(Atom (Constraint (op, FString h))) in
            bound op, bound `Eq
          in
          let has_equal_constraint = function
            | OpamTypes.(Atom (Constraint (`Eq, _))) (* = *) -> true
            | _ -> false
          and has_leq_lt_constraint = function
            | OpamTypes.(Atom (Constraint ((`Lt | `Leq), FString ver)))
              when OpamVersionCompare.compare ver h <= 0
              (* < X or <= X with X <= h *) -> true
            | _ -> false
          and has_geq_constraint = function
            | OpamTypes.(Atom (Constraint (`Geq, FString ver)))
              when OpamVersionCompare.compare ver h = 0
              (* >= X with X = h *) -> true
            | _ -> false
          in
          let add_to_condition = function
            | OpamTypes.Empty -> upper_bound
            | Atom (OpamTypes.Filter f) -> And (Atom (Filter f), upper_bound)
            | Atom (Constraint (relop, f)) as c ->
              if has_equal_constraint c || has_leq_lt_constraint c then
                (* there is = X or <= h, leave it alone *)
                Atom (Constraint (relop, f))
              else if has_geq_constraint c then
                (* there is >= h, add = h *)
                equal_bound
              else
                And (Atom (Constraint (relop, f)), upper_bound)
            | Block a ->
              if has_equal_constraint a || has_leq_lt_constraint a then
                (* there is = X or <= h, leave it alone *)
                Block a
              else if has_geq_constraint a then
                (* there is >= h, add = h *)
                Block equal_bound
              else
                Block (And (a, upper_bound))
            | And (a, b) ->
              (* there is = X or <= h in either part of the conjunction, leave
                 it alone *)
              if has_equal_constraint a || has_equal_constraint b
                 || has_leq_lt_constraint a || has_leq_lt_constraint b
              then
                And (a, b)
              else if has_geq_constraint a || has_geq_constraint b then
                (* there is >= h in either part of the conjunction, add = h *)
                equal_bound
              else
                And (And (a, b), upper_bound)
            | Or (a, b) -> And (Or (a, b), upper_bound)
          in
          let c' = add_to_condition condition in
          OpamFormula.Atom (name, c')
      end
    | Block x -> Block (locked_deps x)
    | And (a, b) -> And (locked_deps a, locked_deps b)
    | Or (a, b) -> Or (locked_deps a, locked_deps b)
  in
  locked_deps current_deps

let adapt_opam opams no_upper_bound git_commit reason opam_fpath opam =
  let ( let* ) = Result.bind in
  let opams = Lazy.force opams in
  let new_deps = adapt_deps no_upper_bound opams opam in
  let opam' = opam_archive git_commit reason new_deps opam_fpath opam in
  let* format_from_string =
    (* this adds the x-opam-repository-commit-hash-at-time-of-archiving
       manually to the string.
       the reasoning is that comments aren't tracked by OpamFile, and sometimes
       the last line is: 'available: false # my important comment' -- and we
       don't want to loose / move the '# my important comment'. if we add
       another token/item at the end of the opam file, the comment will stay
    *)
    let* old_content = Bos.OS.File.read opam_fpath in
    let not_add_nl =
      String.get old_content (String.length old_content - 1) = '\n'
    in
    let tweaked_content =
      let comm = commit_field ^ ":\n  \"" ^ git_commit ^ "\"\n" in
      old_content ^ (if not_add_nl then "" else "\n") ^ comm
    in
    Ok tweaked_content
  in
  let o = OpamFile.make (OpamFilename.raw (Fpath.to_string opam_fpath)) in
  Ok (OpamFile.OPAM.to_string_with_preserved_format ~format_from_string o opam')

let output_opam_diff opam_fpath data =
  let ( let* ) = Result.bind in
  let* tmp = Bos.OS.File.tmp "new_opam_%s" in
  let* () = Bos.OS.File.write tmp data in
  let* diff, _ =
    let cmd =
      let color = match Fmt.style_renderer Fmt.stdout with
        | `Ansi_tty -> "always"
        | `None -> "never"
      in
      Bos.Cmd.(v "diff" % "-u" % ("--color=" ^ color) % p opam_fpath % p tmp)
    in
    Bos.OS.Cmd.(run_out cmd |> out_string)
  in
  Logs.app (fun m -> m "%s@.@." diff);
  Ok ()

let move_opam archive opam_fpath data =
  let ( let* ) = Result.bind in
  let pkg_name, pkg_ver = pkg_name_and_version opam_fpath in
  let target = Fpath.(v archive / "packages" / pkg_name / pkg_ver / "opam") in
  let* _ = Bos.OS.Dir.create (Fpath.parent target) in
  let* () = Bos.OS.File.write target data in
  let* () = Bos.OS.File.delete opam_fpath in
  let* () = Bos.OS.Dir.delete (Fpath.parent opam_fpath) in
  ignore (Bos.OS.Dir.delete (Fpath.parent (Fpath.parent opam_fpath)));
  Ok ()

let opam_matches filter opam =
  match filter with
  | `Unavailable ->
    (* available: false *)
    let available =
      match OpamFile.OPAM.available opam with
      | OpamTypes.FBool b -> b = false
      | _ -> false
    in
    let pkg_name, pkg_ver =
      OpamPackage.Name.to_string (OpamFile.OPAM.name opam),
      OpamPackage.Version.to_string (OpamFile.OPAM.version opam)
    in
    let reason =
      if available then
        Some (pkg_name, pkg_ver, "available: false")
      else
        None
    in
    available, reason
  | `Unmaintained ->
    let pkg_name, pkg_ver =
      OpamPackage.Name.to_string (OpamFile.OPAM.name opam),
      OpamPackage.Version.to_string (OpamFile.OPAM.version opam)
    in
    let maintained =
      match OpamFile.OPAM.extended opam "x-maintained" Fun.id with
      | None -> false
      | Some { pelem = Bool b ; _ } -> b = false
      | Some v ->
        Logs.warn (fun m -> m "%s %s x-maintained: expected a bool, got %s"
                      pkg_name pkg_ver (OpamPrinter.FullPos.value v));
        false
    in
    maintained, Some (pkg_name, pkg_ver, "x-maintained: false")
  | `Ocaml v ->
    (* should return true if there's an upper bound on ocaml <= v *)
    let ocaml_dep = OpamPackage.Name.of_string "ocaml" in
    let deps = OpamFile.OPAM.depends opam in
    let dep_matches op filter =
      match filter with
      | OpamTypes.FString ver ->
        begin
          match op with
          | `Lt -> OpamVersionCompare.compare ver v <= 0
          | `Leq | `Eq -> OpamVersionCompare.compare ver v < 0
          | _ -> false
        end
      | _ -> false
    in
    let rec walk_formula p = function
      | OpamTypes.Empty -> false
      | Atom f -> p f
      | Block formula -> walk_formula p formula
      | And (a, b) -> walk_formula p a || walk_formula p b
      | Or (a, b) -> walk_formula p a && walk_formula p b
    in
    let p = function
      | OpamTypes.Filter _ -> false
      | Constraint (op, filter) -> dep_matches op filter
    in
    let rec find_dep e = function
      | OpamFormula.Empty -> false, e
      | Atom (name, cond) ->
        if OpamPackage.Name.equal ocaml_dep name then
          if walk_formula p cond then
            let e =
              let cond = condition_to_string cond in
              let pkg_name, pkg_ver =
                OpamPackage.Name.to_string (OpamFile.OPAM.name opam),
                OpamPackage.Version.to_string (OpamFile.OPAM.version opam)
              in
              let reason =
                "\"ocaml\"" ^ (if cond = "" then "" else " { " ^ cond ^ " }")
              in
              Some (pkg_name, pkg_ver, reason)
            in
            true, e
          else
            false, e
        else
          false, e
      | Block x -> find_dep e x
      | And (a, b) ->
        let a', ea = find_dep e a in
        let b', eb = find_dep ea b in
        a' || b', eb
      | Or (a, b) ->
        let a', ea = find_dep e a in
        let b', eb = find_dep ea b in
        a' && b', eb
    in
    find_dep None deps

let is_installable opams opam =
  Logs.info (fun m -> m "installable of opam %s version %s"
               (OpamPackage.Name.to_string (OpamFile.OPAM.name opam))
               (OpamPackage.Version.to_string (OpamFile.OPAM.version opam)));
  let find_available name =
    OpamPackage.Set.fold (fun pkg acc ->
        if OpamPackage.Name.equal pkg.OpamPackage.name name then
          (OpamPackage.Version.to_string pkg.OpamPackage.version) :: acc
        else
          acc) opams []
  in
  let current_deps = OpamFile.OPAM.depends opam in
  let rec deps_good e = function
    | OpamFormula.Empty -> true, e
    | Atom (name, condition) ->
      Logs.info (fun m -> m "deps good %s" (OpamPackage.Name.to_string name));
      (* we've to find name in opams, and figure whether condition is satisfied *)
      let all_available = find_available name in
      (* esp. in conjunctions ("foo" {>= "1.0" & < "1.3"}) we need to track the
         matching candidates across the "&" - otherwise we may select "2.0" for
         the first conjunct, and 0.3 for the second. That's why we use a
         reference cell here. *)
      let available = ref all_available in
      let relop_cmp x = function
        | `Eq -> x = 0
        | `Geq -> x >= 0
        | `Gt -> x > 0
        | `Leq -> x <= 0
        | `Lt -> x < 0
        | `Neq -> x <> 0
      in
      let combine_f op a b = match a, b with
        | `Bool a, `Bool b -> `Bool (op a b)
        | `Always, _ | _, `Always -> `Always
      in
      let rec matches_filter = function
        | OpamTypes.FBool b -> `Bool b
        | FString s ->
          Logs.info (fun m -> m "matches_filter: string %s" s);
          `Bool true
        | FIdent (_opt_names, var, _env) ->
          begin match OpamVariable.to_string var with
            | "dev" | "with-doc" | "with-test" | "with-dev-setup" -> `Always
            | "build" | "post" -> `Bool true
            | _ ->
              Logs.info (fun m -> m "matches_filter: ident %s" (OpamVariable.to_string var));
              `Bool true
          end
        | FOp (f, rel, g) ->
          begin match f with
            | FIdent (_, var, _) when OpamVariable.to_string var = "os" ->
              `Bool true
            | _ ->
              Logs.info (fun m -> m "matches_filter: %s %s %s" (filter_to_string f)
                            (string_of_relop rel) (filter_to_string g));
              `Bool true
          end
        | FAnd (f, g) ->
          combine_f ( && ) (matches_filter f) (matches_filter g)
        | FOr (f, g) ->
          combine_f ( || ) (matches_filter f) (matches_filter g)
        | FNot f ->
          begin match matches_filter f with
            | `Bool b -> `Bool (not b)
            | `Always ->
              Logs.info (fun m -> m "matches_filter: not %s resulted in true" (filter_to_string f));
              `Bool true
          end
        | FDefined f ->
          Logs.info (fun m -> m "matches_filter: defined %s" (filter_to_string f));
          `Bool true
        | FUndef f ->
          Logs.info (fun m -> m "matches_filter: undefined %s" (filter_to_string f));
          `Bool true
      in
      let rec matches_condition = function
        | OpamTypes.Empty ->
          Logs.debug (fun m -> m "matches_condition: empty");
          `Bool true
        | Atom (OpamTypes.Filter f) ->
          Logs.debug (fun m -> m "matches_condition: filter %s" (filter_to_string f));
          matches_filter f
        | Atom (Constraint (relop, f)) ->
          Logs.debug (fun m -> m "matches_condition: constraint %s %s"
                        (string_of_relop relop)
                        (filter_to_string f));
          let r =
            let v =
              match f with
              | OpamTypes.FString s -> Some s
              | FIdent (_opt_names, var, _env) when OpamVariable.to_string var = "version" ->
                Some (OpamPackage.Version.to_string (OpamFile.OPAM.version opam))
              | _ -> None
            in
            match v with
            | None ->
              Logs.info (fun m -> m "matches_condition: unexpected filter %s"
                            (filter_to_string f));
              true
            | Some v ->
              available :=
                List.filter (fun ver ->
                    let r = relop_cmp (OpamVersionCompare.compare ver v) relop in
                    Logs.debug (fun m -> m "%s %s %s = %B" ver (string_of_relop relop) v r);
                    r)
                  !available;
              !available <> []
          in
          Logs.debug (fun m -> m "matches_condition result %B" r);
          `Bool r
        | Block a ->
          Logs.debug (fun m -> m "matches_condition: block");
          matches_condition a
        | And (a, b) ->
          Logs.debug (fun m -> m "matches_condition: and");
          let a = matches_condition a in
          let b = matches_condition b in
          Logs.debug (fun m -> m "matches_condition: and - combining %s with %s"
                         (match a with `Bool true -> "bool true" | `Bool false -> "bool false" | `Always -> "always")
                         (match b with `Bool true -> "bool true" | `Bool false -> "bool false" | `Always -> "always"));
          let r = combine_f ( && ) a b in
          Logs.debug (fun m -> m "matches_condition: and result %s"
                         (match r with `Bool true -> "bool true" | `Bool false -> "bool false" | `Always -> "always"));
          r
        | Or (a, b) ->
          Logs.debug (fun m -> m "matches_condition: or");
          let a = matches_condition a in
          available := all_available;
          let b = matches_condition b in
          available := all_available;
          combine_f ( || ) a b
      in
      let r =
        match matches_condition condition with
        | `Bool b -> b && !available <> []
        | `Always -> true
      in
      let e =
        if not r then begin
          let cond = condition_to_string condition in
          let pkg_name, pkg_ver =
            OpamPackage.Name.to_string (OpamFile.OPAM.name opam),
            OpamPackage.Version.to_string (OpamFile.OPAM.version opam)
          in
          let reason =
            "\"" ^ OpamPackage.Name.to_string name ^ "\"" ^
            (if cond = "" then "" else " { " ^ cond ^ " }")
          in
          Some (pkg_name, pkg_ver, reason)
        end else
          e
      in
      r, e
    | Block x -> deps_good e x
    | And (a, b) ->
      let a', ea = deps_good e a in
      let b', eb = deps_good ea b in
      a' && b', eb
    | Or (a, b) ->
      let a', ea = deps_good e a in
      let b', eb = deps_good ea b in
      a' || b', eb
  in
  deps_good None current_deps

module FS = Set.Make(Fpath)

let filter_and_reason ~unavailable ~unmaintained ~ocaml_lower_bound ~installable
    ~pkg_all pkgs =
  let err n =
    "only either --" ^ n ^ " or --installable can be provided"
  in
  match unavailable, unmaintained, ocaml_lower_bound with
  | true, false, None ->
    if installable then
      invalid_arg (err "unavailable")
    else
      `Unavailable, Uninstallable
  | false, true, None ->
    if installable then
      invalid_arg (err "unmaintained")
    else
      `Unmaintained, Maintenance_intent
  | false, false, Some v ->
    if installable then
      invalid_arg (err "ocaml")
    else
      `Ocaml v, OCaml_version
  | false, false, None ->
    if S.is_empty pkgs && not pkg_all then
      invalid_arg "one of --unavailable, --unmaintained, --ocaml, \
                   --pkg/--pkg-file/--pkg-all must be specified"
    else if installable then
      `Installable, Uninstallable
    else
      `Package, Uninstallable
  | _ ->
    failwith "only one of --unavailable, --unmaintained, or --ocaml bound allowed"

let jump () unavailable unmaintained ocaml_lower_bound
    ignore_pkgs no_upper_bound opam_repository archive dry_run pkgs user_reason
    include_diff no_summary installable pkg_file pkg_all later_installable
    iters commit =
  let ( let* ) = Result.bind in
  let pkg_dir = Fpath.(v opam_repository / "packages") in
  let* _ = Bos.OS.Dir.must_exist pkg_dir in
  let* git_commit =
    match commit with
    | None ->
      let cmd = Bos.Cmd.(v "git" % "rev-parse" % "HEAD") in
      Bos.OS.Cmd.(run_out cmd |> out_string ~trim:true |> success)
    | Some x -> Ok x
  in
  let* _ =
    if dry_run then
      Ok ()
    else
      let* _ = Bos.OS.Dir.must_exist (Fpath.v archive) in
      Ok ()
  in
  let ignored_pkgs = S.of_list ignore_pkgs in
  let* pkgs = match pkgs, pkg_file with
    | [], None -> Ok S.empty
    | _ :: _, None -> Ok (S.of_list pkgs)
    | [], Some f ->
      let* data = Bos.OS.File.read (Fpath.v f) in
      let pkgs =
        String.split_on_char '\n' data |>
        String.concat " " |>
        String.split_on_char ' ' |>
        List.filter (fun s -> s <> "") |>
        S.of_list
      in
      Ok pkgs
    | _, Some _ ->
      failwith "only --pkg or --pkg-file allowed"
  in
  if later_installable && S.is_empty pkgs && not pkg_all then
    invalid_arg "--later-installable present, but no --pkg/--pkg-file/--pkg-all";
  let all_opams =
    lazy
      (OpamPackage.keys
         (OpamRepositoryState.load_opams_from_dir
            (OpamRepositoryName.of_string "temporary")
            (OpamFilename.Dir.of_string opam_repository)))
  in
  let no_upper_bound =
    OpamPackage.Name.Set.of_list
      (List.map OpamPackage.Name.of_string no_upper_bound)
  in
  let filter, default_reason =
    filter_and_reason ~unavailable ~unmaintained ~ocaml_lower_bound ~installable
      ~pkg_all pkgs
  in
  let reason = match user_reason with
    | None -> (fun _fpath -> default_reason)
    | Some reason -> (fun _fpath -> reason)
  in
  (* keeping a set of opam files we moved, important for printing a summary,
     but also for dry_run (and bookkeeping in "opams" and "pkgs") to avoid
     considering an opam file we already deleted. *)
  let moved_files = ref FS.empty in
  let should_consider pkgs path =
    if Fpath.filename path = "opam" && not (FS.mem path !moved_files) then
      let name, version = pkg_name_and_version path in
      if S.mem version ignored_pkgs || S.mem name ignored_pkgs then
        (Logs.info (fun m -> m "ignoring %a (--ignore)" pp_pkg path) ;
         None)
      else if S.is_empty pkgs || S.mem name pkgs || S.mem version pkgs then
        let opam =
          let opam_file =
            OpamFile.make (OpamFilename.raw (Fpath.to_string path))
          in
          OpamFile.OPAM.read opam_file
        in
        (* check for x-maintained being true *)
        let maintained =
          match OpamFile.OPAM.extended opam "x-maintained" Fun.id with
          | None -> false
          | Some { pelem = Bool b ; _ } -> b
          | Some v ->
            Logs.warn (fun m -> m "%a x-maintained: expected a bool, got %s"
                          pp_pkg path (OpamPrinter.FullPos.value v));
            false
        in
        if maintained then
          (Logs.info (fun m -> m "ignoring %a (x-maintained is true)" pp_pkg path);
           None)
        else
          Some (version, opam)
      else
        None
    else
      None
  in
  let explanations = Hashtbl.create 7 in
  let foreach opams pkgs filter reason path acc =
    let* () = acc in
    let archive_it =
      match should_consider pkgs path with
      | None -> None
      | Some (pkg_version, opam) ->
        Logs.info (fun m -> m "dealing with %s" pkg_version);
        let r, exp =
          match filter with
          | `Unavailable | `Unmaintained | `Ocaml _ as f -> opam_matches f opam
          | `Package ->
            let name, ver =
              let first_dot = String.index pkg_version '.' in
              String.sub pkg_version 0 first_dot,
              String.sub pkg_version (first_dot + 1) (String.length pkg_version - first_dot - 1)
            in
            true, Some (name, ver, "--pkg command line")
          | `Installable ->
            let r, exp = is_installable (Lazy.force opams) opam in
            not r, exp
        in
        if r then begin
          (match exp with
           | None -> ()
           | Some (pkg, ver, reason) ->
             let others = match Hashtbl.find_opt explanations pkg with
               | None -> []
               | Some acc -> acc
             in
             Hashtbl.replace explanations pkg ((ver, reason) :: others));
          Some opam
        end else
          None
    in
    match archive_it with
    | None -> Ok ()
    | Some opam ->
      Logs.app (fun m -> m "archiving %a" Fmt.(styled (`Fg `Red) pp_pkg) path);
      moved_files := FS.add path !moved_files;
      if not include_diff && dry_run then
        Ok ()
      else
        let* new_opam_content =
          adapt_opam all_opams no_upper_bound git_commit reason path opam
        in
        let* () =
          if include_diff then
            output_opam_diff path new_opam_content
          else
            Ok ()
        in
        let* () =
          if not dry_run then
            move_opam archive path new_opam_content
          else
            Ok ()
        in
        Ok ()
  in
  let* r =
    Bos.OS.Dir.fold_contents (foreach all_opams pkgs filter reason) (Ok ()) pkg_dir
  in
  (* if we're "later_installable", adjust the filter and reason *)
  let filter, reason =
    if later_installable then
      `Installable, (fun _ -> Uninstallable)
    else
      filter, reason
  in
  (* fixpoint if packages and `Installable - needs to modify "opams" *)
  let adjust_pkgs_opams pkgs opams =
    (* update the available opam files in the OpamPackage.Set *)
    let opams =
      lazy
        (FS.fold (fun pkg opams ->
             let _, ver = pkg_name_and_version pkg in
             OpamPackage.Set.remove (OpamPackage.of_string ver) opams)
            !moved_files (Lazy.force opams))
    (* update the pkgs *)
    and pkgs =
      FS.fold (fun p pkgs ->
          let _, ver = pkg_name_and_version p in
          S.remove ver pkgs)
        !moved_files pkgs
    in
    (pkgs, opams)
  in
  let rec go r (pkgs, opams) n i =
    Logs.app (fun m -> m "go %u moved files %u" i (FS.cardinal !moved_files));
    match r with
    | Error _ as e -> e
    | Ok () ->
      if n = 0 then
        r
      else
        let old_count = FS.cardinal !moved_files in
        let* r =
          Bos.OS.Dir.fold_contents (foreach opams pkgs filter reason) (Ok ()) pkg_dir
        in
        let pkgs, opams = adjust_pkgs_opams pkgs opams in
        (* if we made progress (removed some more), continue *)
        if FS.cardinal !moved_files > old_count &&
           (not (S.is_empty pkgs) || pkg_all)
        then
          go r (pkgs, opams) (pred n) (succ i)
        else
          r
  in
  let r =
    if FS.is_empty !moved_files || filter <> `Installable then
      Ok ()
    else
      go r (adjust_pkgs_opams pkgs all_opams) iters 0
  in
  (* we print a summary *)
  if not no_summary then begin
    let h = Hashtbl.create 13 in
    FS.iter (fun path ->
        let name, vers = pkg_name_and_version path in
        let have = Option.value ~default:S.empty (Hashtbl.find_opt h name) in
        Hashtbl.replace h name (S.add vers have))
      !moved_files;
    Logs.app (fun m -> m "@.Summary (%u unique packages, %u total opam files):"
                 (Hashtbl.length h) (FS.cardinal !moved_files));
    Hashtbl.fold (fun pkg v acc -> (pkg, v) :: acc) h []
    |> List.sort (fun (a, _) (b, _) -> String.compare a b)
    |> List.iter (fun (pkg, vers) ->
        let plen = String.length pkg + 1 in
        let vers_without_pkg v =
          String.sub v plen (String.length v - plen)
        in
        let vers =
          S.map vers_without_pkg vers
          |> S.elements
          |> List.sort OpamVersionCompare.compare
        in
        Logs.app (fun m -> m "- %s: %a" pkg Fmt.(list ~sep:(any ", ") string)
                     vers));
    if Hashtbl.length explanations > 0 then begin
      Logs.app (fun m -> m "@.Reasoning:");
      Hashtbl.fold (fun pkg r acc -> (pkg, r) :: acc) explanations []
      |> List.sort (fun (a, _) (b, _) -> String.compare a b)
      |> List.iter (fun (pkg_name, ver_reas) ->
          List.sort (fun (va, _) (vb, _) -> OpamVersionCompare.compare va vb) ver_reas
        |> List.iter (fun (version, reason) ->
              Logs.app (fun m -> m "- \"%s.%s\" unsatisfied dependency: %s" pkg_name version reason)))
    end;
  end;
  r

let setup_log style_renderer level =
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  Logs.set_reporter (Logs_fmt.reporter ~dst:Format.std_formatter ())

open Cmdliner

let setup_log =
  Term.(const setup_log
        $ Fmt_cli.style_renderer ()
        $ Logs_cli.level ())

let unavailable =
  let doc =
    "Filter unavailable packages where the field 'available' is 'false'"
  in
  Arg.(value & flag & info ~doc ["unavailable"])

let unmaintained =
  let doc =
    "Filter unmaintained packages where the field 'x-maintained' is 'false'"
  in
  Arg.(value & flag & info ~doc ["unmaintained"])

let ocaml_lower_bound =
  let doc = "Filter packages depending on OCaml smaller than X" in
  Arg.(value & opt (some string) None & info ~doc ["ocaml-lower-bound"])

let ignore_pkgs =
  let doc = "Ignore this package" in
  let def = [ "arch-x86_32" ; "ocaml-option-spacetime" ; "conf-freeglut" ; "ocamlmig" ] in
  Arg.(value & opt_all string def & info ~doc ["ignore"])

let no_upper_bound =
  let doc = "Do not emit an upper bound for dependencies to this package" in
  Arg.(value & opt_all string ["ocaml"]  & info ~doc ["no-upper-bound"])

let opam_repository =
  let doc = "Opam repository directory to work on (must be a git checkout)" in
  Arg.(value & opt dir "." & info ~doc ["opam-repository"])

let opam_repository_archive =
  let doc = "Opam repository archive directory to work on" in
  Arg.(value & opt string "../opam-repository-archive" &
       info ~doc ~docv:"DIR" ["opam-repository-archive"])

let dry_run =
  let doc = "Do not modify anything, just print what would be done" in
  Arg.(value & flag & info ~doc ["dryrun" ; "dry-run"])

let include_diff =
  let doc = "Output the diffs on the console as well" in
  Arg.(value & flag & info ~doc ["include-diff"])

let no_summary =
  let doc = "Don't output a summary on the console" in
  Arg.(value & flag & info ~doc ["no-summary"])

let pkg =
  let doc = "Archive this package (may be package name or package.version)" in
  Arg.(value & opt_all string [] & info ~doc ["pkg"])

let pkg_all =
  let doc = "Consider all packages" in
  Arg.(value & flag & info ~doc ["pkg-all"])

let pkg_file =
  let doc = "Archive packages from the file (package name or package.version)" in
  Arg.(value & opt (some file) None & info ~doc ["pkg-file"])

let installable =
  let doc =
    "Check for installability of the provided packages \
     (--pkg or --pkg-file or --pkg-all must be provided)."
  in
  Arg.(value & flag & info ~doc ["installable"])

let reason =
  let doc =
    "Reason for archival (default is uninstallable). If ocaml-lower-bound is \
     provided, ocaml-version is used by default."
  in
  Arg.(value & opt (some (enum reason_enum)) None & info ~doc ["reason"])

let later_installable =
  let doc =
    "Check after the initial run for installability of the provided packages \
     (--pkg or --pkg-file or --pkg-all must be provided)."
  in
  Arg.(value & flag & info ~doc ["later-installable"])

let iters =
  let doc = "How many iterations to do for installability" in
  Arg.(value & opt int Int.max_int & info ~doc ["iters"])

let commit =
  let doc = "Which git commit to use for \
             x-opam-repository-commit-hash-at-time-of-archiving (defaults to \
             `git rev-parse HEAD`)"
  in
  Arg.(value & opt (some string) None & info ~doc ["commit"])

let cmd =
  let info = Cmd.info "archive-opam" ~version:"%%VERSION_NUM%%"
  and term =
    Term.(term_result (const jump $ setup_log $ unavailable $ unmaintained
                       $ ocaml_lower_bound
                       $ ignore_pkgs $ no_upper_bound $ opam_repository
                       $ opam_repository_archive $ dry_run $ pkg
                       $ reason $ include_diff $ no_summary $ installable
                       $ pkg_file $ pkg_all $ later_installable $ iters
                       $ commit))
  in
  Cmd.v info term

let () = exit (Cmd.eval cmd)
