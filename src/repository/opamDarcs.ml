(**************************************************************************)
(*                                                                        *)
(*    Copyright 2012-2015 OCamlPro                                        *)
(*    Copyright 2012 INRIA                                                *)
(*                                                                        *)
(*  All rights reserved. This file is distributed under the terms of the  *)
(*  GNU Lesser General Public License version 2.1, with the special       *)
(*  exception on linking described in the file LICENSE.                   *)
(*                                                                        *)
(**************************************************************************)

open OpamTypes
open OpamFilename.Op
open OpamProcess.Job.Op

module Darcs = struct

  let name = `darcs

  let exists repo =
    OpamFilename.exists_dir (repo.repo_root / "_darcs")

  let darcs repo =
    let dir = OpamFilename.Dir.to_string repo.repo_root in
    fun ?verbose ?env args ->
      OpamSystem.make_command ~dir ?verbose ?env "darcs" args

  let init repo =
    OpamProcess.Job.of_list
      [ darcs repo [ "init" ];
        darcs repo [ "get" ; OpamUrl.base_url repo.repo_url; "--lazy" ] ]
    @@+ function
    | None -> Done ()
    | Some (_,err) -> OpamSystem.process_error err

  (* With darcs, it is apparently easier to compute a diff between
     remote and local, without fething at all. So we set fetch to be a
     no-op. *)
  let fetch _ =
    Done ()

  (* Merge is actually a full pull *)
  let reset repo =
    darcs repo [ "pull"; OpamUrl.base_url repo.repo_url; "--all"; "--quiet" ]
    @@> fun r ->
    OpamSystem.raise_on_process_error r;
    Done ()

  (* Difference between remote and local is a 'pull --dry-run' *)
  let diff repo =
    darcs repo [ "pull" ; OpamUrl.base_url repo.repo_url; "--dry-run" ; "--quiet" ]
    @@> fun r ->
    OpamSystem.raise_on_process_error r;
    Done (r.OpamProcess.r_stdout <> [])

  let revision _ =
    Done "<darcs-???>"

  let versionned_files repo =
    darcs repo [ "show" ; "files" ]
    @@> fun r ->
    OpamSystem.raise_on_process_error r;
    Done r.OpamProcess.r_stdout

  let vc_dir repo = OpamFilename.Op.(repo.repo_root / "_darcs")

end

module B = OpamVCS.Make(Darcs)
