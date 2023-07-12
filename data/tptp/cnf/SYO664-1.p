%------------------------------------------------------------------------------
% File     : SYO664-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_2_4_1
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_2_4_1 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.3.0
% Syntax   : Number of clauses     :   10 (   2 unt;   4 nHn;   9 RR)
%            Number of literals    :   48 (   0 equ;  37 neg)
%            Maximal clause size   :   14 (   4 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   17 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_37,axiom,
    ( ~ 'E'(s('0'),f(suc(B_45)))
    | ~ 'E'(s('0'),f(B_45))
    | ~ 'E'(s('0'),f(suc(B_46)))
    | ~ 'E'(s('0'),f(suc(B_43)))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(s('0'),f(B_43))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s('0'),f(B_46))
    | ~ 'E'(s('0'),f(B_44))
    | ~ iLEQ(suc(B_45),suc(B_46))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s('0'),f(suc(B_44))) ) ).

cnf(clause_70,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_20,axiom,
    ( ~ 'LE'(f(B_42),s(s('0')))
    | 'E'(s('0'),f(B_42))
    | 'LE'(f(B_42),s('0')) ) ).

cnf(clause_66,axiom,
    ( ~ 'E'('0',f(B_63))
    | ~ 'E'('0',f(suc(B_61)))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_61))
    | ~ iLEQ(suc(B_61),suc(B_62))
    | ~ 'E'('0',f(suc(B_63)))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(B_62),suc(B_63))
    | ~ 'E'('0',f(B_64))
    | ~ iLEQ(suc(B_63),suc(B_64))
    | ~ 'E'('0',f(suc(B_62)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'('0',f(suc(B_64)))
    | ~ 'E'('0',f(B_62)) ) ).

cnf(clause_58,axiom,
    'LE'(f(A),s(s('0'))) ).

cnf(clause_6,axiom,
    ( ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_117,axiom,
    ( ~ 'LE'(f(suc(B_60)),s('0'))
    | 'E'('0',f(suc(B_60)))
    | 'LE'(f(B_60),'0') ) ).

cnf(clause_94,axiom,
    ( ~ 'LE'(f(B_60),s('0'))
    | 'E'('0',f(B_60))
    | 'LE'(f(B_60),'0') ) ).

cnf(clause_50,axiom,
    ( ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_83,axiom,
    ( ~ 'LE'(f(suc(B_42)),s(s('0')))
    | 'E'(s('0'),f(suc(B_42)))
    | 'LE'(f(B_42),s('0')) ) ).

%------------------------------------------------------------------------------
