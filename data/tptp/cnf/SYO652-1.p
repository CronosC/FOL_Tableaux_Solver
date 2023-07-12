%------------------------------------------------------------------------------
% File     : SYO652-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_1_3_2
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_1_3_2 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.3.0
% Syntax   : Number of clauses     :   23 (   2 unt;  15 nHn;  22 RR)
%            Number of literals    :  292 (   0 equ; 250 neg)
%            Maximal clause size   :   19 (  12 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   70 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_35,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ 'E'('0',f(suc(suc(B_13))))
    | ~ 'E'(f(B_13),f(suc(B_13)))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_133,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ 'E'('0',f(suc(suc(B_13))))
    | ~ 'E'(f(B_13),f(suc(B_13)))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_16,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(B_12)))
    | 'E'(f(B_13),f(suc(B_13))) ) ).

cnf(clause_149,axiom,
    ( ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_141,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_13),f(suc(B_13))) ) ).

cnf(clause_199,axiom,
    'LE'(f(A),s('0')) ).

cnf(clause_191,axiom,
    ( ~ 'LE'(f(suc(B_10)),s('0'))
    | 'E'('0',f(suc(B_10)))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_74,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ 'E'('0',f(suc(suc(B_13))))
    | ~ 'E'(f(B_13),f(suc(B_13)))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_5,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_13),f(suc(B_13))) ) ).

cnf(clause_181,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ 'E'('0',f(suc(suc(B_13))))
    | ~ 'E'(f(B_13),f(suc(B_13)))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_96,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ 'E'('0',f(suc(suc(B_13))))
    | ~ 'E'(f(B_13),f(suc(B_13)))
    | ~ iLEQ(suc(B_11),suc(B_12)) ) ).

cnf(clause_17,axiom,
    ( ~ 'LE'(f(B_10),s('0'))
    | 'E'('0',f(B_10))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_50,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_12),f(suc(B_12)))
    | 'E'(f(B_13),f(suc(B_13))) ) ).

cnf(clause_3,axiom,
    ( ~ 'LE'(f(suc(suc(B_10))),s('0'))
    | 'E'('0',f(suc(suc(B_10))))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_45,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_13),f(suc(B_13))) ) ).

cnf(clause_99,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_76,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_13),f(suc(B_13))) ) ).

cnf(clause_61,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ 'E'('0',f(suc(suc(B_13))))
    | ~ 'E'(f(B_13),f(suc(B_13)))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_68,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(B_12)))
    | 'E'(f(B_13),f(suc(B_13))) ) ).

cnf(clause_91,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ 'E'('0',f(suc(suc(B_13))))
    | ~ 'E'(f(B_13),f(suc(B_13)))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_183,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_12),f(suc(B_12)))
    | 'E'(f(B_13),f(suc(B_13))) ) ).

cnf(clause_44,axiom,
    ( ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_100,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ iLEQ(suc(B_12),suc(B_13))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(B_13))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ 'E'('0',f(suc(B_13)))
    | ~ 'E'('0',f(B_12))
    | ~ 'E'('0',f(suc(suc(B_13))))
    | ~ 'E'(f(B_13),f(suc(B_13)))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

%------------------------------------------------------------------------------
