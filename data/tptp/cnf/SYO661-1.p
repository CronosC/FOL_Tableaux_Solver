%------------------------------------------------------------------------------
% File     : SYO661-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_2_2_2
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_2_2_2 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.3.0
% Syntax   : Number of clauses     :   28 (   2 unt;  16 nHn;  27 RR)
%            Number of literals    :  238 (   0 equ; 195 neg)
%            Maximal clause size   :   14 (   8 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   59 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_93,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_147,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_51,axiom,
    ( ~ 'LE'(f(suc(suc(B_17))),s('0'))
    | 'E'('0',f(suc(suc(B_17))))
    | 'LE'(f(B_17),'0') ) ).

cnf(clause_106,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_8,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12)) ) ).

cnf(clause_72,axiom,
    'LE'(f(A),s(s('0'))) ).

cnf(clause_119,axiom,
    ( ~ 'LE'(f(suc(B_10)),s(s('0')))
    | 'E'(s('0'),f(suc(B_10)))
    | 'LE'(f(B_10),s('0')) ) ).

cnf(clause_57,axiom,
    ( ~ 'LE'(f(suc(B_17)),s('0'))
    | 'E'('0',f(suc(B_17)))
    | 'LE'(f(B_17),'0') ) ).

cnf(clause_0,axiom,
    ( ~ 'LE'(f(B_17),s('0'))
    | 'E'('0',f(B_17))
    | 'LE'(f(B_17),'0') ) ).

cnf(clause_85,axiom,
    ( ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_131,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_180,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_18,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_213,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_109,axiom,
    ( ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_135,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_86,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_204,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_125,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(B_18)))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_20,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(B_18)))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_35,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_148,axiom,
    ( ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_33,axiom,
    ( ~ 'LE'(f(suc(suc(B_10))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_10))))
    | 'LE'(f(B_10),s('0')) ) ).

cnf(clause_133,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_118,axiom,
    ( ~ 'LE'(f(B_10),s(s('0')))
    | 'E'(s('0'),f(B_10))
    | 'LE'(f(B_10),s('0')) ) ).

cnf(clause_161,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_139,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_25,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

%------------------------------------------------------------------------------
