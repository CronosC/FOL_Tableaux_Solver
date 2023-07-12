%------------------------------------------------------------------------------
% File     : SYO650-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_1_2_3
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_1_2_3 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.3.0
% Syntax   : Number of clauses     :   36 (   2 unt;  26 nHn;  35 RR)
%            Number of literals    :  463 (   0 equ; 395 neg)
%            Maximal clause size   :   20 (  12 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   89 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_338,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_150,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_7),f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_7)))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_437,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_7),f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_7)))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_211,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_436,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_419,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(suc(B_6))))
    | 'E'(f(B_7),f(suc(suc(B_7)))) ) ).

cnf(clause_278,axiom,
    ( ~ 'LE'(f(B_5),s('0'))
    | 'E'('0',f(B_5))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_217,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(B_7),f(suc(suc(B_7)))) ) ).

cnf(clause_129,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_7),f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_7)))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_406,axiom,
    'LE'(f(A),s('0')) ).

cnf(clause_359,axiom,
    ( ~ 'LE'(f(suc(suc(B_5))),s('0'))
    | 'E'('0',f(suc(suc(B_5))))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_109,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_110,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_7),f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_7)))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_189,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_309,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_6),f(suc(suc(B_6))))
    | 'E'(f(B_7),f(suc(suc(B_7)))) ) ).

cnf(clause_145,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(B_7),f(suc(suc(B_7)))) ) ).

cnf(clause_447,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_7),f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_7)))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_24,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_7),f(suc(suc(B_7)))) ) ).

cnf(clause_313,axiom,
    ( ~ 'LE'(f(suc(B_5)),s('0'))
    | 'E'('0',f(suc(B_5)))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_2,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(suc(B_6))))
    | 'E'(f(B_7),f(suc(suc(B_7)))) ) ).

cnf(clause_333,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_376,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_5)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_5)))))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_308,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_7),f(suc(suc(B_7)))) ) ).

cnf(clause_135,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_7),f(suc(suc(B_7))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(suc(B_7)))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6))) ) ).

cnf(clause_319,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_7),f(suc(suc(B_7))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(suc(B_7)))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_345,axiom,
    ( ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_282,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_7),f(suc(suc(B_7)))) ) ).

cnf(clause_206,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_253,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_7),f(suc(suc(B_7))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(suc(B_7)))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_88,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_7),f(suc(suc(B_7))))
    | ~ 'E'('0',f(suc(suc(suc(B_7)))))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_167,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(suc(B_6))))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_441,axiom,
    ( ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_6),f(suc(suc(B_6))))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_416,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_64,axiom,
    ( ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_451,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(suc(B_6))))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_371,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'('0',f(suc(B_7)))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_6),suc(B_7))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(B_7))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(B_7),f(suc(suc(B_7)))) ) ).

%------------------------------------------------------------------------------
