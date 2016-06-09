(**************************************************************************)
(*                                                                        *)
(*    Copyright 2015 OCamlPro                                             *)
(*                                                                        *)
(*  All rights reserved. This file is distributed under the terms of the  *)
(*  GNU Lesser General Public License version 2.1, with the special       *)
(*  exception on linking described in the file LICENSE.                   *)
(*                                                                        *)
(**************************************************************************)

open OpamTypes

type t = {
  cudf_file: string option;
  solver_timeout: float;
  external_solver: OpamTypes.arg list option Lazy.t;
  solver_preferences_default: string Lazy.t option;
  solver_preferences_upgrade: string Lazy.t option;
  solver_preferences_fixup: string Lazy.t option;
}

type 'a options_fun =
  ?cudf_file:string option ->
  ?solver_timeout:float ->
  ?external_solver:OpamTypes.arg list option Lazy.t ->
  ?solver_preferences_default:string Lazy.t option ->
  ?solver_preferences_upgrade:string Lazy.t option ->
  ?solver_preferences_fixup:string Lazy.t option ->
  'a

let default =
  let external_solver = lazy (
    if OpamSystem.command_exists "aspcud" then Some [CIdent "aspcud", None] else
    if OpamSystem.command_exists "packup" then Some [CIdent "packup", None] else
    if OpamSystem.command_exists "mccs" then Some [CIdent "mccs", None] else
      None
  ) in
  {
    cudf_file = None;
    solver_timeout = 5.;
    external_solver;
    solver_preferences_default = None;
    solver_preferences_upgrade = None;
    solver_preferences_fixup = None;
  }

let setk k t
    ?cudf_file
    ?solver_timeout
    ?external_solver
    ?solver_preferences_default
    ?solver_preferences_upgrade
    ?solver_preferences_fixup
  =
  let (+) x opt = match opt with Some x -> x | None -> x in
  k {
    cudf_file = t.cudf_file + cudf_file;
    solver_timeout = t.solver_timeout + solver_timeout;
    external_solver = t.external_solver + external_solver;
    solver_preferences_default =
      t.solver_preferences_default + solver_preferences_default;
    solver_preferences_upgrade =
      t.solver_preferences_upgrade + solver_preferences_upgrade;
    solver_preferences_fixup =
      t.solver_preferences_fixup + solver_preferences_fixup;
  }

let set t = setk (fun x () -> x) t

let r = ref default

let update ?noop:_ = setk (fun cfg () -> r := cfg) !r

let solver_kind_of_string = function
  | "aspcud" -> Some `aspcud
  | "mccs" -> Some `mccs
  | "packup" -> Some `packup
  | _ -> None

let solver_args = [
  `aspcud,
  [ CIdent "input", None; CIdent "output", None; CIdent "criteria", None ];
  `mccs,
  [ CString "-i", None; CIdent "input", None;
    CString "-o", None; CIdent "output", None;
    CString "-lexagregate[%{criteria}%]", None];
  `packup,
  [ CIdent "input", None; CIdent "output", None;
    CString "-u", None; CIdent "criteria", None ];
]

let solver_of_cmd cmd =
  let solver_opt =
    match cmd with
    | (exe, None) :: _ ->
      let base = match exe with
        | CString s -> Filename.basename s
        | CIdent i -> i
      in
      solver_kind_of_string base
    | _ -> None
  in
  OpamStd.Option.Op.(solver_opt +! `aspcud)

let external_solver_command ~input ~output ~criteria =
  let open OpamStd.Option.Op in
  Lazy.force !r.external_solver >>| fun cmd ->
  let cmd = match cmd with
    | [exe] -> exe :: List.assoc (solver_of_cmd cmd) solver_args
    | cmd -> cmd
  in
  OpamFilter.single_command (fun v ->
      if not (OpamVariable.Full.is_global v) then None else
      match OpamVariable.to_string (OpamVariable.Full.variable v) with
      | "aspcud" -> Some (S "aspcud")
      | "mccs" -> Some (S "mccs")
      | "packup" -> Some (S "packup")
      | "input" -> Some (S input)
      | "output" -> Some (S output)
      | "criteria" -> Some (S criteria)
      | _ -> None)
    cmd

type criteria = {
  crit_default: string;
  crit_upgrade: string;
  crit_fixup: string;
}

let default_criteria_compat = {
 crit_default = "-removed,-notuptodate,-changed";
 crit_upgrade = "-removed,-notuptodate,-changed";
 crit_fixup = "-changed,-notuptodate";
}

let default_criteria_mccs = {
  crit_default = "-removed,\
                  -count[version-lag:,true],\
                  -changed,\
                  -count[version-lag:,false],\
                  -new";
  crit_upgrade = "-removed,\
                  -count[version-lag:,false],\
                  -new";
  crit_fixup = "-changed,-count[version-lag:,false]";
}

let default_criteria_packup = default_criteria_compat

let default_criteria_aspcud19 = {
  crit_default = "-count(removed),\
                  -notuptodate(request),-sum(request,version-lag),\
                  -count(down),\
                  -notuptodate(changed),-count(changed),\
                  -notuptodate(solution),-sum(solution,version-lag)";
  crit_upgrade = "-count(down),\
                  -count(removed),\
                  -notuptodate(solution),-sum(solution,version-lag),\
                  -count(new)";
  crit_fixup = "-count(changed),\
                -notuptodate(solution),-sum(solution,version-lag)";
}

let check_aspcud_version = function
  | (_, Some _) :: _ | [] -> `Compat
  | ((CString cmdname | CIdent cmdname), None) :: _ ->
    let log fmt = OpamConsole.log "SOLVER" fmt in
    try
      log "Checking version of criteria accepted by the external solver";
      (* Run with closed stdin to workaround bug in some solver scripts *)
      match
        OpamSystem.read_command_output ~verbose:false ~allow_stdin:false
          [cmdname; "-v"]
      with
      | [] ->
        log "No response from 'solver -v', using compat criteria";
        `Compat
      | s::_ ->
        match OpamStd.String.split s ' ' with
        | "aspcud"::_::v::_ when OpamVersionCompare.compare v "1.9" >= 0 ->
          log "Solver is aspcud > 1.9: using latest version criteria";
          `Latest
        | _ ->
          log "Solver isn't aspcud > 1.9, using compat criteria";
          `Compat
    with OpamSystem.Process_error _ ->
      log "Solver doesn't know about '-v': using compat criteria";
      `Compat

let with_auto_criteria config =
  let open OpamStd.Option.Op in
  match Lazy.force config.external_solver with
  | None -> config
  | Some solver_cmd ->
    let criteria = match solver_of_cmd solver_cmd with
      | `mccs -> lazy (default_criteria_mccs)
      | `packup -> lazy (default_criteria_packup)
      | `aspcud ->
        lazy (match check_aspcud_version solver_cmd with
            | `Latest -> default_criteria_aspcud19
            | `Compat -> default_criteria_compat)
    in
    set config
      ~solver_preferences_default:
        (config.solver_preferences_default >>+ fun () ->
         Some (lazy (Lazy.force criteria).crit_default))
      ~solver_preferences_upgrade:
        (config.solver_preferences_upgrade >>+ fun () ->
         Some (lazy (Lazy.force criteria).crit_upgrade))
      ~solver_preferences_fixup:
        (config.solver_preferences_fixup >>+ fun () ->
         Some (lazy (Lazy.force criteria).crit_fixup))
      ()

let initk k =
  let open OpamStd.Config in
  let open OpamStd.Option.Op in
  let external_solver =
    let disable = function
      | true -> Some (lazy None)
      | false -> None
    in
    env_bool "USEINTERNALSOLVER" >>= disable >>+ fun () ->
    env_bool "NOASPCUD" >>= disable >>+ fun () ->
    env_string "EXTERNALSOLVER" >>| function
    | "" -> lazy None
    | s ->
      lazy (
        let args = OpamStd.String.split s ' ' in
        Some (List.map (fun a -> OpamTypes.CString a, None) args)
      )
  in
  let criteria =
    env_string "CRITERIA" >>| fun c -> Some (lazy c) in
  let upgrade_criteria =
    (env_string "UPGRADECRITERIA" >>| fun c -> Some (lazy c)) ++ criteria in
  let fixup_criteria =
    env_string "FIXUPCRITERIA" >>| fun c -> Some (lazy c) in
  setk (setk (fun c -> r := with_auto_criteria c; k)) !r
    ~cudf_file:(env_string "CUDFFILE")
    ?solver_timeout:(env_float "SOLVERTIMEOUT")
    ?external_solver
    ?solver_preferences_default:criteria
    ?solver_preferences_upgrade:upgrade_criteria
    ?solver_preferences_fixup:fixup_criteria

let init ?noop:_ = initk (fun () -> ())

let criteria kind =
  let crit = match kind with
    | `Default -> !r.solver_preferences_default
    | `Upgrade -> !r.solver_preferences_upgrade
    | `Fixup -> !r.solver_preferences_fixup
  in
  match crit with
  | Some (lazy c) -> c
  | None -> failwith "Solver criteria uninitialised"
