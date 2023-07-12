%--------------------------------------------------------------------------
% File     : SWV018-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Software Verification
% Problem  : Fact 8 of the Neumann-Stubblebine analysis
% Version  : [Wei99] axioms.
% English  :

% Refs     : [Wei99] Weidenbach (1999), Towards and Automatic Analysis of S
%            [Bau99] Baumgartner (1999), FTP'2000 - Problem Sets
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v5.5.0, 0.25 v5.4.0, 0.44 v5.3.0, 0.29 v5.0.0, 0.25 v4.1.0, 0.29 v4.0.0, 0.25 v3.5.0, 0.43 v3.4.0, 0.50 v3.3.0, 0.33 v3.2.0, 0.40 v3.1.0, 0.29 v2.7.0, 0.00 v2.6.0, 0.50 v2.5.0, 0.67 v2.4.0
% Syntax   : Number of clauses     :   41 (  14 unt;   0 nHn;  38 RR)
%            Number of literals    :   89 (   0 equ;  50 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    6 (   1 avg)
%            Number of predicates  :   12 (  12 usr;   0 prp; 1-1 aty)
%            Number of functors    :   17 (  17 usr;   7 con; 0-4 aty)
%            Number of variables   :   82 (  29 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created by tptp2X -f tptp -t cnf:otter SWV018+1.p
%--------------------------------------------------------------------------
cnf(a_is_party_of_protocol_2,axiom,
    party_of_protocol(a) ).

cnf(a_sent_message_i_to_b_3,axiom,
    message(sent(a,b,pair(a,an_a_nonce))) ).

cnf(a_stored_message_i_4,axiom,
    a_stored(pair(b,an_a_nonce)) ).

cnf(a_forwards_secure_5,axiom,
    ( message(sent(a,A,pair(E,encrypt(F,C))))
    | ~ a_stored(pair(A,B))
    | ~ message(sent(t,a,triple(encrypt(quadruple(A,B,C,D),at),E,F))) ) ).

cnf(b_hold_key_bt_for_t_7,axiom,
    b_holds(key(bt,t)) ).

cnf(b_is_party_of_protocol_8,axiom,
    party_of_protocol(b) ).

cnf(nonce_a_is_fresh_to_b_9,axiom,
    fresh_to_b(an_a_nonce) ).

cnf(b_creates_freash_nonces_in_time_10,axiom,
    ( message(sent(b,t,triple(b,generate_b_nonce(B),encrypt(triple(A,B,generate_expiration_time(B)),bt))))
    | ~ fresh_to_b(B)
    | ~ message(sent(A,b,pair(A,B))) ) ).

cnf(b_creates_freash_nonces_in_time_11,axiom,
    ( b_stored(pair(A,B))
    | ~ fresh_to_b(B)
    | ~ message(sent(A,b,pair(A,B))) ) ).

cnf(b_accepts_secure_session_key_12,axiom,
    ( b_holds(key(B,A))
    | ~ a_key(B)
    | ~ b_stored(pair(A,C))
    | ~ message(sent(A,b,pair(encrypt(triple(A,B,generate_expiration_time(C)),bt),encrypt(generate_b_nonce(C),B)))) ) ).

cnf(t_holds_key_at_for_a_13,axiom,
    t_holds(key(at,a)) ).

cnf(t_holds_key_bt_for_b_14,axiom,
    t_holds(key(bt,b)) ).

cnf(t_is_party_of_protocol_15,axiom,
    party_of_protocol(t) ).

cnf(server_t_generates_key_16,axiom,
    ( message(sent(t,C,triple(encrypt(quadruple(A,D,generate_key(D),E),G),encrypt(triple(C,generate_key(D),E),F),B)))
    | ~ a_nonce(D)
    | ~ message(sent(A,t,triple(A,B,encrypt(triple(C,D,E),F))))
    | ~ t_holds(key(G,C))
    | ~ t_holds(key(F,A)) ) ).

cnf(intruder_can_record_17,axiom,
    ( intruder_message(C)
    | ~ message(sent(A,B,C)) ) ).

cnf(intruder_decomposes_pairs_18,axiom,
    ( intruder_message(A)
    | ~ intruder_message(pair(A,B)) ) ).

cnf(intruder_decomposes_pairs_19,axiom,
    ( intruder_message(B)
    | ~ intruder_message(pair(A,B)) ) ).

cnf(intruder_decomposes_triples_20,axiom,
    ( intruder_message(A)
    | ~ intruder_message(triple(A,B,C)) ) ).

cnf(intruder_decomposes_triples_21,axiom,
    ( intruder_message(B)
    | ~ intruder_message(triple(A,B,C)) ) ).

cnf(intruder_decomposes_triples_22,axiom,
    ( intruder_message(C)
    | ~ intruder_message(triple(A,B,C)) ) ).

cnf(intruder_decomposes_quadruples_23,axiom,
    ( intruder_message(A)
    | ~ intruder_message(quadruple(A,B,C,D)) ) ).

cnf(intruder_decomposes_quadruples_24,axiom,
    ( intruder_message(B)
    | ~ intruder_message(quadruple(A,B,C,D)) ) ).

cnf(intruder_decomposes_quadruples_25,axiom,
    ( intruder_message(C)
    | ~ intruder_message(quadruple(A,B,C,D)) ) ).

cnf(intruder_decomposes_quadruples_26,axiom,
    ( intruder_message(D)
    | ~ intruder_message(quadruple(A,B,C,D)) ) ).

cnf(intruder_composes_pairs_27,axiom,
    ( intruder_message(pair(A,B))
    | ~ intruder_message(B)
    | ~ intruder_message(A) ) ).

cnf(intruder_composes_triples_28,axiom,
    ( intruder_message(triple(A,B,C))
    | ~ intruder_message(C)
    | ~ intruder_message(B)
    | ~ intruder_message(A) ) ).

cnf(intruder_composes_quadruples_29,axiom,
    ( intruder_message(quadruple(A,B,C,D))
    | ~ intruder_message(D)
    | ~ intruder_message(C)
    | ~ intruder_message(B)
    | ~ intruder_message(A) ) ).

cnf(intruder_interception_30,axiom,
    ( intruder_message(B)
    | ~ intruder_holds(key(B,C))
    | ~ intruder_message(encrypt(A,B))
    | ~ party_of_protocol(C) ) ).

cnf(intruder_message_sent_31,axiom,
    ( message(sent(B,C,A))
    | ~ intruder_message(A)
    | ~ party_of_protocol(C)
    | ~ party_of_protocol(B) ) ).

cnf(intruder_holds_key_32,axiom,
    ( intruder_holds(key(A,B))
    | ~ intruder_message(A)
    | ~ party_of_protocol(B) ) ).

cnf(intruder_key_encrypts_33,axiom,
    ( intruder_message(encrypt(A,B))
    | ~ intruder_holds(key(B,C))
    | ~ intruder_message(A)
    | ~ party_of_protocol(C) ) ).

cnf(an_a_nonce_is_a_nonce_34,axiom,
    a_nonce(an_a_nonce) ).

cnf(generated_times_and_nonces_are_nonces_36,axiom,
    a_nonce(generate_expiration_time(A)) ).

cnf(generated_times_and_nonces_are_nonces_37,axiom,
    a_nonce(generate_b_nonce(A)) ).

cnf(nothing_is_a_nonce_and_a_key_38,axiom,
    ( ~ a_key(A)
    | ~ a_nonce(A) ) ).

cnf(generated_keys_are_keys_39,axiom,
    a_key(generate_key(A)) ).

cnf(an_intruder_nonce_is_a_fresh_intruder_nonce_40,axiom,
    fresh_intruder_nonce(an_intruder_nonce) ).

cnf(can_generate_more_fresh_intruder_nonces_41,axiom,
    ( fresh_intruder_nonce(generate_intruder_nonce(A))
    | ~ fresh_intruder_nonce(A) ) ).

cnf(fresh_intruder_nonces_are_fresh_to_b_42,axiom,
    ( fresh_to_b(A)
    | ~ fresh_intruder_nonce(A) ) ).

cnf(fresh_intruder_nonces_are_fresh_to_b_43,axiom,
    ( intruder_message(A)
    | ~ fresh_intruder_nonce(A) ) ).

cnf(co1_44,negated_conjecture,
    ( ~ b_holds(key(A,C))
    | ~ intruder_holds(key(A,B)) ) ).

%--------------------------------------------------------------------------