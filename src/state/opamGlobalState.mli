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

(** Loading and handling of the global state of an opam root *)

open OpamTypes
open OpamStateTypes

(** Loads the global state (from the opam root obtained through
    [OpamStateConfig.(!r.root)]) *)
val load: 'a lock -> 'a global_state

(** Loads the global state as [load], and calls the given function while keeping
    it locked (as per the [lock] argument), releasing the lock afterwards *)
val with_: 'a lock -> ('a global_state -> 'b) -> 'b

(** The set of all installed packages, in any switch *)
val all_installed: 'a global_state -> package_set

val fold_switches:
  (switch -> switch_selections -> 'a -> 'a) -> 'b global_state -> 'a -> 'a

(** Returns the map of installed instances of the package name towards the list
    of switches they are installed in *)
val installed_versions: 'a global_state -> name -> switch list package_map

(** List of configured repositories ordered by decreasing priority (note: this
    is at the moment global, but it's planned that switches can define their own
    subset and order of the repos) *)
val repos_list: 'a global_state -> repository_name list

(** Releases any locks on the given global_state *)
val unlock: 'a global_state -> unlocked global_state

(** Calls the provided function, ensuring a temporary write lock on the given
    global state*)
val with_write_lock:
  ?dontblock:bool -> 'a global_state -> (rw global_state -> 'c) -> 'c

(** Writes back the global configuration file ~/.opam/config *)
val write: rw global_state -> unit
