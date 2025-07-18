module DY.TwoMessage.Run

open DY.Core
open DY.Lib
open DY.Simplified

open DY.TwoMessage.Protocol

open DY.TwoMessage.Run.Printing

val run:
  unit -> traceful (option unit)
let run () =
  let alice = "Alice" in
  let bob = "Bob" in

  let* (alice_sid, ping_ts) = send_ping alice bob in
  let*? (bob_sid, ack_ts) =
    receive_ping_and_send_ack bob ping_ts in
  receive_ack alice ack_ts;*?


  let* tr = get_trace in
  let _ = IO.debug_print_string "************* Trace *************\n" in
  let _ = IO.debug_print_string (
   trace_to_string get_trace_to_string_printers tr
 ) in

  return (Some ())

let _ = run () empty_trace
