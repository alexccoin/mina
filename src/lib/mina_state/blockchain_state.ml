open Core_kernel
open Mina_base
open Snark_params.Tick

module Poly = struct
  [%%versioned
  module Stable = struct
    module V1 = struct
      type ('staged_ledger_hash, 'snarked_ledger_hash, 'token_id, 'time) t =
        { staged_ledger_hash : 'staged_ledger_hash
        ; snarked_ledger_hash : 'snarked_ledger_hash
        ; genesis_ledger_hash : 'snarked_ledger_hash
        ; snarked_next_available_token : 'token_id
        ; timestamp : 'time
        }
      [@@deriving sexp, fields, equal, compare, hash, yojson, hlist]
    end
  end]
end

[%%define_locally
Poly.
  ( staged_ledger_hash
  , snarked_ledger_hash
  , genesis_ledger_hash
  , snarked_next_available_token
  , timestamp
  , to_hlist
  , of_hlist )]

module Value = struct
  [%%versioned
  module Stable = struct
    module V1 = struct
      type t =
        ( Staged_ledger_hash.Stable.V1.t
        , Frozen_ledger_hash.Stable.V1.t
        , Token_id.Stable.V1.t
        , Block_time.Stable.V1.t )
        Poly.Stable.V1.t
      [@@deriving sexp, equal, compare, hash, yojson]

      let to_latest = Fn.id
    end
  end]
end

type var =
  ( Staged_ledger_hash.var
  , Frozen_ledger_hash.var
  , Token_id.var
  , Block_time.Checked.t )
  Poly.t

let create_value ~staged_ledger_hash ~snarked_ledger_hash ~genesis_ledger_hash
    ~snarked_next_available_token ~timestamp =
  { Poly.staged_ledger_hash
  ; snarked_ledger_hash
  ; genesis_ledger_hash
  ; snarked_next_available_token
  ; timestamp
  }

let data_spec =
  let open Data_spec in
  [ Staged_ledger_hash.typ
  ; Frozen_ledger_hash.typ
  ; Frozen_ledger_hash.typ
  ; Token_id.typ
  ; Block_time.Checked.typ
  ]

let typ : (var, Value.t) Typ.t =
  Typ.of_hlistable data_spec ~var_to_hlist:to_hlist ~var_of_hlist:of_hlist
    ~value_to_hlist:to_hlist ~value_of_hlist:of_hlist

let var_to_input
    ({ staged_ledger_hash
     ; snarked_ledger_hash
     ; genesis_ledger_hash
     ; snarked_next_available_token
     ; timestamp
     } :
      var) =
  let open Random_oracle.Input.Chunked in
  List.reduce_exn ~f:append
    [ Staged_ledger_hash.var_to_input staged_ledger_hash
    ; field (Frozen_ledger_hash.var_to_hash_packed snarked_ledger_hash)
    ; field (Frozen_ledger_hash.var_to_hash_packed genesis_ledger_hash)
    ; Token_id.Checked.to_input snarked_next_available_token
    ; Block_time.Checked.to_input timestamp
    ]

let to_input
    ({ staged_ledger_hash
     ; snarked_ledger_hash
     ; genesis_ledger_hash
     ; snarked_next_available_token
     ; timestamp
     } :
      Value.t) =
  let open Random_oracle.Input.Chunked in
  List.reduce_exn ~f:append
    [ Staged_ledger_hash.to_input staged_ledger_hash
    ; field (snarked_ledger_hash :> Field.t)
    ; field (genesis_ledger_hash :> Field.t)
    ; Token_id.to_input snarked_next_available_token
    ; Block_time.to_input timestamp
    ]

let set_timestamp t timestamp = { t with Poly.timestamp }

let negative_one
    ~(constraint_constants : Genesis_constants.Constraint_constants.t)
    ~(consensus_constants : Consensus.Constants.t) ~genesis_ledger_hash
    ~snarked_next_available_token : Value.t =
  let genesis_ledger_hash =
    Frozen_ledger_hash.of_ledger_hash genesis_ledger_hash
  in
  { staged_ledger_hash =
      Staged_ledger_hash.genesis ~constraint_constants ~genesis_ledger_hash
  ; snarked_ledger_hash = genesis_ledger_hash
  ; genesis_ledger_hash
  ; snarked_next_available_token
  ; timestamp = consensus_constants.genesis_state_timestamp
  }

(* negative_one and genesis blockchain states are equivalent *)
let genesis = negative_one

type display = (string, string, string, string) Poly.t [@@deriving yojson]

let display
    Poly.
      { staged_ledger_hash
      ; snarked_ledger_hash
      ; genesis_ledger_hash
      ; snarked_next_available_token
      ; timestamp
      } =
  { Poly.staged_ledger_hash =
      Visualization.display_prefix_of_string @@ Ledger_hash.to_base58_check
      @@ Staged_ledger_hash.ledger_hash staged_ledger_hash
  ; snarked_ledger_hash =
      Visualization.display_prefix_of_string
      @@ Frozen_ledger_hash.to_base58_check snarked_ledger_hash
  ; genesis_ledger_hash =
      Visualization.display_prefix_of_string
      @@ Frozen_ledger_hash.to_base58_check genesis_ledger_hash
  ; snarked_next_available_token =
      Token_id.to_string snarked_next_available_token
  ; timestamp =
      Time.to_string_trimmed ~zone:Time.Zone.utc (Block_time.to_time timestamp)
  }
