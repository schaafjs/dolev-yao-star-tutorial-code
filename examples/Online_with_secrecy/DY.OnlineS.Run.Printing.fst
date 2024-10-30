module DY.OnlineS.Run.Printing

open DY.Core
open DY.Lib
open Comparse
open DY.OnlineS.Protocol

/// Helper functions for trace printing.
/// Here we define how our abstract message and state types
/// should be printed.


val message_to_string: bytes -> option string
let message_to_string b =
  match? parse message b with
  | Ping p -> Some (Printf.sprintf "Ping [name = (%s), n_a = (%s)]" (p.p_alice) (bytes_to_string p.p_n_a))
  | Ack a -> Some (Printf.sprintf "Ping [n_a = (%s)]" (bytes_to_string a.a_n_a))


val state_to_string: bytes -> option string
let state_to_string b =
  match? parse state b with
  | SentPing p -> Some (Printf.sprintf "SentPing [to = (%s), n_a = (%s)]" p.sp_bob (bytes_to_string p.sp_n_a))
  | SentAck a -> Some (Printf.sprintf "SentAck [to = (%s), n_a = (%s)]" a.sa_alice (bytes_to_string a.sa_n_a))
  | ReceivedAck r -> Some (Printf.sprintf "ReceivedAck [from = (%s), n_a = (%s)]" r.ra_bob (bytes_to_string r.ra_n_a))




val get_trace_to_string_printers: trace_to_string_printers
let get_trace_to_string_printers  = 
  trace_to_string_printers_builder 
    message_to_string
    [(local_state_state.tag, state_to_string)]
    []
