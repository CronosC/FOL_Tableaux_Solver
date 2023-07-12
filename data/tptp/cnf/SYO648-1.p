%------------------------------------------------------------------------------
% File     : SYO648-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_1_1_4
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_1_1_4 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.3.0
% Syntax   : Number of clauses     :   27 (   2 unt;  17 nHn;  26 RR)
%            Number of literals    :  244 (   0 equ; 202 neg)
%            Maximal clause size   :   17 (   9 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   42 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_113,axiom,
    ( ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_260,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_1)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_1)))))
    | 'LE'(f(B_1),'0') ) ).

cnf(clause_48,axiom,
    ( ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_79,axiom,
    ( ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_2),f(suc(suc(B_2)))) ) ).

cnf(clause_90,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_2),f(suc(suc(suc(B_2))))) ) ).

cnf(clause_326,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_203,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_2),f(suc(suc(suc(B_2))))) ) ).

cnf(clause_299,axiom,
    'LE'(f(A),s('0')) ).

cnf(clause_157,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_328,axiom,
    ( ~ 'LE'(f(suc(B_1)),s('0'))
    | 'E'('0',f(suc(B_1)))
    | 'LE'(f(B_1),'0') ) ).

cnf(clause_217,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_2),f(suc(suc(suc(B_2))))) ) ).

cnf(clause_44,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_72,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_168,axiom,
    ( ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_231,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_1))))),s('0'))
    | 'E'('0',f(suc(suc(suc(suc(B_1))))))
    | 'LE'(f(B_1),'0') ) ).

cnf(clause_46,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_278,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_254,axiom,
    ( ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_114,axiom,
    ( ~ 'LE'(f(suc(suc(B_1))),s('0'))
    | 'E'('0',f(suc(suc(B_1))))
    | 'LE'(f(B_1),'0') ) ).

cnf(clause_223,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_2),f(suc(suc(suc(B_2))))) ) ).

cnf(clause_160,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_277,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_2),f(suc(suc(B_2)))) ) ).

cnf(clause_29,axiom,
    ( ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_2),f(suc(suc(B_2)))) ) ).

cnf(clause_145,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1)))))) ) ).

cnf(clause_221,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_2),f(suc(suc(B_2)))) ) ).

cnf(clause_62,axiom,
    ( ~ 'LE'(f(B_1),s('0'))
    | 'E'('0',f(B_1))
    | 'LE'(f(B_1),'0') ) ).

cnf(clause_237,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1))))) ) ).

%------------------------------------------------------------------------------
