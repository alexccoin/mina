open Core
open Async
open Integration_test_lib

module Make (Inputs : Intf.Test.Inputs_intf) = struct
  open Inputs
  open Engine
  open Dsl

  (* TODO: find a way to avoid this type alias (first class module signatures restrictions make this tricky) *)
  type network = Network.t

  type node = Network.Node.t

  type dsl = Dsl.t

  let config =
    let open Test_config in
    let open Test_config.Block_producer in
    { default with
      requires_graphql =
        true
        (* must have at least as many block producers as party's in any
           Parties.t, because we need that many keypairs
        *)
    ; block_producers =
        [ { balance = "4000000000"; timing = Untimed }
        ; { balance = "4000000000"; timing = Untimed }
        ; { balance = "4000000000"; timing = Untimed }
        ; { balance = "4000000000"; timing = Untimed }
        ; { balance = "4000000000"; timing = Untimed }
        ; { balance = "4000000000"; timing = Untimed }
        ; { balance = "4000000000"; timing = Untimed }
        ; { balance = "4000000000"; timing = Untimed }
        ]
    ; num_snark_workers = 0
    }

  let run network t =
    let open Malleable_error.Let_syntax in
    let logger = Logger.create () in
    let block_producer_nodes = Network.block_producers network in
    let%bind () =
      Malleable_error.List.iter block_producer_nodes
        ~f:(Fn.compose (wait_for t) Wait_condition.node_to_initialize)
    in
    let node = List.hd_exn block_producer_nodes in
    let%map () =
      section "send a snapp"
        (let (user_cmd : Mina_base.User_command.t), _, _, _ =
           Quickcheck.random_value
             (Mina_base.User_command_generators.parties_with_ledger ())
         in
         let parties0 =
           match user_cmd with
           | Parties p ->
               p
           | Signed_command _ ->
               failwith "Expected a Parties command"
         in
         (* the generated parties0 has a fee payer with a public
            key not found in the integration test ledger, so
            we replace that key and generate a new signature
         *)
         let%bind fee_payer_pk = Util.pub_key_of_node node in
         let%bind fee_payer_sk = Util.priv_key_of_node node in
         Format.eprintf "FEE PAYER PK: %s@."
           (Signature_lib.Public_key.Compressed.to_base58_check fee_payer_pk) ;
         Format.eprintf "OTHER PKS: %s@."
           ( List.map parties0.other_parties ~f:(fun party ->
                 Signature_lib.Public_key.Compressed.to_base58_check
                   party.data.body.public_key)
           |> String.concat ~sep:", " ) ;
         Format.eprintf "OTHER PARTIES FULL COMMITMENT: %s@."
           ( List.map parties0.other_parties ~f:(fun party ->
                 Bool.to_string party.data.body.use_full_commitment)
           |> String.concat ~sep:", " ) ;
         (* substitute valid public keys for fee payer, other parties *)
         let parties_valid_pk =
           { parties0 with
             fee_payer =
               { parties0.fee_payer with
                 data =
                   { parties0.fee_payer.data with
                     body =
                       { parties0.fee_payer.data.body with
                         public_key = fee_payer_pk
                       }
                   }
               }
           }
         in
         let fee_payer_hash =
           Mina_base.Party.Predicated.of_fee_payer
             parties_valid_pk.fee_payer.data
           |> Mina_base.Party.Predicated.digest
         in
         let fee_payer_signature =
           Signature_lib.Schnorr.Chunked.sign fee_payer_sk
             (Random_oracle.Input.Chunked.field
                ( Mina_base.Parties.commitment parties_valid_pk
                |> Mina_base.Parties.Transaction_commitment.with_fee_payer
                     ~fee_payer_hash ))
         in
         (* substitute valid signature for fee payer *)
         let parties_valid_fee_payer_signature =
           { parties_valid_pk with
             fee_payer =
               { parties_valid_pk.fee_payer with
                 authorization = fee_payer_signature
               }
           }
         in
         (* we need to update the other parties signatures, if there's a full commitment,
            which relies on the fee payer hash, which differs from that used when parties0
            was generated
         *)
         let other_parties_hash =
           Mina_base.Parties.Party_or_stack.With_hashes.other_parties_hash
             parties_valid_fee_payer_signature.other_parties
         in
         let protocol_state_predicate_hash =
           Mina_base.Snapp_predicate.Protocol_state.digest
             parties_valid_fee_payer_signature.fee_payer.data.body
               .protocol_state
         in
         let memo_hash =
           Mina_base.Signed_command_memo.hash
             parties_valid_fee_payer_signature.memo
         in
         let tx_commitment =
           Mina_base.Parties.Transaction_commitment.create ~other_parties_hash
             ~protocol_state_predicate_hash ~memo_hash
         in
         let full_tx_commitment =
           Mina_base.Parties.Transaction_commitment.with_fee_payer tx_commitment
             ~fee_payer_hash
         in
         let sign_for_other_party ~use_full_commitment sk =
           let commitment =
             if use_full_commitment then full_tx_commitment else tx_commitment
           in
           Signature_lib.Schnorr.Chunked.sign sk
             (Random_oracle.Input.Chunked.field commitment)
         in
         let other_parties_with_valid_signatures =
           List.map parties_valid_fee_payer_signature.other_parties
             ~f:(fun { data; authorization } ->
               let authorization_with_valid_signature =
                 match authorization with
                 | Mina_base.Control.Signature _dummy ->
                     let pk = data.body.public_key in
                     let sk =
                       match
                         Signature_lib.Public_key.Compressed.Map.find keymap pk
                       with
                       | Some sk ->
                           sk
                       | None ->
                           failwithf
                             "gen_from: Could not find secret key for public \
                              key %s in keymap"
                             (Signature_lib.Public_key.Compressed
                              .to_base58_check pk)
                             ()
                     in
                     let use_full_commitment = data.body.use_full_commitment in
                     let signature =
                       sign_for_other_party ~use_full_commitment sk
                     in
                     Mina_base.Control.Signature signature
                 | Proof _ | None_given ->
                     authorization
               in
               { Mina_base.Party.data
               ; authorization = authorization_with_valid_signature
               })
         in
         let parties_valid =
           { parties_valid_fee_payer_signature with
             other_parties = other_parties_with_valid_signatures
           }
         in
         [%log info] "Sending valid snapp" ;
         let%bind () =
           match%bind.Deferred
             Network.Node.send_snapp ~logger node ~parties:parties_valid
           with
           | Ok () ->
               [%log info] "Snapps transaction succeeded" ;
               Malleable_error.return ()
           | Error err ->
               let err_str = Error.to_string_mach err in
               [%log error] "Error sending snapp"
                 ~metadata:[ ("error", `String err_str) ] ;
               Malleable_error.soft_error_format ~value:()
                 "Error sending snapp: %s" err_str
         in
         return ())
      (* let parties_bad_signature =
           { parties0 with
             fee_payer =
               { parties_valid_pk.fee_payer with
                 authorization = Mina_base.Signature.dummy
               }
           }
         in
         [%log info] "Sending snapp with invalid signature";
         match%bind.Deferred Network.Node.send_snapp ~logger node ~parties:parties_bad_signature with
         | Ok () ->
             [%log error]
               "Snapps transaction succeeded, expected failure due to invalid \
                signature" ;
             Malleable_error.soft_error_format ~value:()
               "Snapps transaction succeeded despite invalid signature"
         | Error err ->
             let err_str = Error.to_string_mach err in
             if String.is_substring ~substring:"Invalid_signature" err_str then (
               [%log info] "Snapps failed as expected with invalid signature" ;
               Malleable_error.return () )
             else (
               [%log error]
                 "Error sending snapp, for a reason other than the expected \
                  invalid signature"
                 ~metadata:[ ("error", `String err_str) ] ;
               Malleable_error.soft_error_format ~value:()
                 "Snapp failed in unexpected way: %s" err_str )) *)
    in
    ()
end
