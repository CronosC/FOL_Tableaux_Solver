%------------------------------------------------------------------------------
% File     : SYO666-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_2_5_1
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_2_5_1 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   10 (   2 unt;   4 nHn;   9 RR)
%            Number of literals    :   54 (   0 equ;  43 neg)
%            Maximal clause size   :   17 (   5 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   19 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_102,axiom,
    ( ~ iLEQ(suc(B_96),suc(B_97))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_96)))
    | ~ iLEQ(suc(B_97),suc(B_98))
    | ~ 'E'('0',f(suc(B_97)))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(B_97))
    | ~ iLEQ(suc(B_95),suc(B_96))
    | ~ 'E'('0',f(B_96))
    | ~ iLEQ(suc(B_94),suc(B_95))
    | ~ 'E'('0',f(suc(B_98)))
    | ~ 'E'('0',f(B_94))
    | ~ iLEQ(suc(A_2),suc(B_94))
    | ~ 'E'('0',f(suc(B_95)))
    | ~ 'E'('0',f(B_98))
    | ~ 'E'('0',f(B_95)) ) ).

cnf(clause_12,axiom,
    ( ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_98,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_123,axiom,
    ( ~ 'LE'(f(suc(B_93)),s('0'))
    | 'E'('0',f(suc(B_93)))
    | 'LE'(f(B_93),'0') ) ).

cnf(clause_42,axiom,
    ( ~ 'LE'(f(B_93),s('0'))
    | 'E'('0',f(B_93))
    | 'LE'(f(B_93),'0') ) ).

cnf(clause_83,axiom,
    'LE'(f(A),s(s('0'))) ).

cnf(clause_70,axiom,
    ( ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_29,axiom,
    ( ~ 'LE'(f(suc(B_68)),s(s('0')))
    | 'E'(s('0'),f(suc(B_68)))
    | 'LE'(f(B_68),s('0')) ) ).

cnf(clause_185,axiom,
    ( ~ 'LE'(f(B_68),s(s('0')))
    | 'E'(s('0'),f(B_68))
    | 'LE'(f(B_68),s('0')) ) ).

cnf(clause_179,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ iLEQ(suc(B_71),suc(B_72))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ 'E'(s('0'),f(B_71))
    | ~ 'E'(s('0'),f(suc(B_71)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ iLEQ(suc(B_72),suc(B_73))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ 'E'(s('0'),f(B_73))
    | ~ 'E'(s('0'),f(suc(B_72)))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(s('0'),f(B_72))
    | ~ 'E'(s('0'),f(suc(B_73))) ) ).

%------------------------------------------------------------------------------
