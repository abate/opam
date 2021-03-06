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

(** Configuration init and handling of downloading commands *)

(** downloads a file from an URL, using Curl, Wget, or a custom configured
    tool, to the given directory. Returns the downloaded filename.
    FIXME: The source OpamFilename.t is indeed a URL. *)
val download:
  overwrite:bool -> ?compress:bool -> ?checksum:string ->
  OpamUrl.t -> OpamFilename.Dir.t ->
  OpamFilename.t OpamProcess.job

(** As [download], but with a specified output filename. *)
val download_as:
  overwrite:bool -> ?compress:bool -> ?checksum:string ->
  OpamUrl.t -> OpamFilename.t ->
  unit OpamProcess.job
