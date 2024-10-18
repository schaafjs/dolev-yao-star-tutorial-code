module DY.TwoMessage.Run

open DY.Core
open DY.Lib

open DY.TwoMessage.Run.Printing
open DY.TwoMessage.Protocol

let run () : traceful (option unit ) =
  let _ = IO.debug_print_string "************* Trace *************\n" in
  
  let alice = "alice" in
  let bob = "bob" in

  let* (alice_sid, ping_ts) = send_ping alice bob in
  let*? (bob_sid, ack_ts) = receive_ping_and_send_ack___ bob ping_ts in
  let*? _ = receive_ack alice ack_ts in

  let* tr = get_trace in
  let _ = IO.debug_print_string (
      trace_to_string get_trace_to_string_printers tr
    ) in

  return (Some ())
  
let _ = run () Nil
