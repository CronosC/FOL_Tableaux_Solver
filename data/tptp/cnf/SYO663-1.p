%------------------------------------------------------------------------------
% File     : SYO663-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_2_3_2
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_2_3_2 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.33 v7.3.0
% Syntax   : Number of clauses     :   44 (   2 unt;  30 nHn;  43 RR)
%            Number of literals    :  582 (   0 equ; 499 neg)
%            Maximal clause size   :   19 (  13 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  139 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_1,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'('0',f(B_38))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_38),f(suc(B_38))) ) ).

cnf(clause_197,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'(f(B_38),f(suc(B_38)))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(suc(B_38))))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'('0',f(B_38))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_458,axiom,
    ( ~ 'LE'(f(B_35),s('0'))
    | 'E'('0',f(B_35))
    | 'LE'(f(B_35),'0') ) ).

cnf(clause_12,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(suc(B_24)))) ) ).

cnf(clause_284,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_55,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_312,axiom,
    ( ~ 'LE'(f(suc(suc(B_23))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_23))))
    | 'LE'(f(B_23),s('0')) ) ).

cnf(clause_324,axiom,
    ( ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_40,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'(f(B_38),f(suc(B_38)))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(suc(B_38))))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'('0',f(B_38))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_36),f(suc(B_36))) ) ).

cnf(clause_236,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'(f(B_38),f(suc(B_38)))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(suc(B_38))))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'('0',f(B_38))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_216,axiom,
    'LE'(f(A),s(s('0'))) ).

cnf(clause_136,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'('0',f(B_38))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_38),f(suc(B_38))) ) ).

cnf(clause_48,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'('0',f(B_38))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_38),f(suc(B_38))) ) ).

cnf(clause_87,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(suc(B_24))))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_539,axiom,
    ( ~ 'LE'(f(suc(B_35)),s('0'))
    | 'E'('0',f(suc(B_35)))
    | 'LE'(f(B_35),'0') ) ).

cnf(clause_297,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'(f(B_38),f(suc(B_38)))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(suc(B_38))))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'('0',f(B_38))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_578,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'(f(B_38),f(suc(B_38)))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(suc(B_38))))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'('0',f(B_38))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_329,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(suc(B_24))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_325,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'('0',f(B_38))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(B_37)))
    | 'E'(f(B_38),f(suc(B_38))) ) ).

cnf(clause_434,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(suc(B_24))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_189,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'('0',f(B_38))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(B_37)))
    | 'E'(f(B_38),f(suc(B_38))) ) ).

cnf(clause_377,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_24),f(suc(B_24)))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_619,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'('0',f(B_38))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_37),f(suc(B_37)))
    | 'E'(f(B_38),f(suc(B_38))) ) ).

cnf(clause_59,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'(f(B_38),f(suc(B_38)))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(suc(B_38))))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'('0',f(B_38))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(B_36))) ) ).

cnf(clause_371,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_24),f(suc(B_24)))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_292,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_93,axiom,
    ( ~ 'LE'(f(suc(suc(B_35))),s('0'))
    | 'E'('0',f(suc(suc(B_35))))
    | 'LE'(f(B_35),'0') ) ).

cnf(clause_207,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'('0',f(B_38))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_38),f(suc(B_38))) ) ).

cnf(clause_467,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(B_24),f(suc(B_24)))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_327,axiom,
    ( ~ 'LE'(f(B_23),s(s('0')))
    | 'E'(s('0'),f(B_23))
    | 'LE'(f(B_23),s('0')) ) ).

cnf(clause_593,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'(f(B_38),f(suc(B_38)))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(suc(B_38))))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'('0',f(B_38))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ iLEQ(suc(B_36),suc(B_37)) ) ).

cnf(clause_176,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(B_24),f(suc(B_24)))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_268,axiom,
    ( ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_448,axiom,
    ( ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_632,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'(f(B_38),f(suc(B_38)))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(suc(B_38))))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'('0',f(B_38))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_581,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_24),f(suc(B_24)))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_43,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_282,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(suc(B_24))))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_123,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(suc(B_24))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_435,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(suc(B_24))))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_160,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(suc(B_24))))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_564,axiom,
    ( ~ 'LE'(f(suc(B_23)),s(s('0')))
    | 'E'(s('0'),f(suc(B_23)))
    | 'LE'(f(B_23),s('0')) ) ).

cnf(clause_607,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ 'E'(s('0'),f(B_24))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s('0'),f(A_1))
    | ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_24)))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(B_24),f(suc(B_24)))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_357,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(B_37),suc(B_38))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ iLEQ(suc(A_2),suc(B_36))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'('0',f(suc(B_38)))
    | ~ 'E'('0',f(B_38))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_37),f(suc(B_37)))
    | 'E'(f(B_38),f(suc(B_38))) ) ).

%------------------------------------------------------------------------------
