module DY.Simplified

open Comparse
open DY.Core
open DY.Lib

val recv_msg_same_trace:
  i:timestamp -> tr:trace ->
  Lemma
  (ensures (
    let (opt_msg, tr_out) = recv_msg i tr in
    tr_out == tr))
  [SMTPat (recv_msg i tr)
  ]
let recv_msg_same_trace i tr =
  normalize_term_spec recv_msg
