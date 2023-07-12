%------------------------------------------------------------------------------
% File     : SYO673-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_3_3_2
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_3_3_2 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.33 v7.3.0
% Syntax   : Number of clauses     :   65 (   2 unt;  45 nHn;  64 RR)
%            Number of literals    :  872 (   0 equ; 748 neg)
%            Maximal clause size   :   19 (  13 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  208 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_618,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_69),f(suc(B_69)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_1370,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'(f(B_81),f(suc(B_81)))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

cnf(clause_981,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_69),f(suc(B_69)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_1288,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | 'E'(f(B_44),f(suc(B_44)))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_104,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_44),f(suc(B_44)))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_44))))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_1497,axiom,
    'LE'(f(A),s(s(s('0')))) ).

cnf(clause_345,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1452,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'(f(B_81),f(suc(B_81)))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

cnf(clause_625,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'(f(B_81),f(suc(B_81))) ) ).

cnf(clause_1113,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | 'E'(f(B_43),f(suc(B_43)))
    | 'E'(f(B_44),f(suc(B_44)))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_1074,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ 'E'('0',f(suc(suc(B_81))))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(B_80),f(suc(B_80))) ) ).

cnf(clause_594,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(B_43))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_44),f(suc(B_44)))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_1397,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_80))))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ 'E'('0',f(suc(suc(B_81))))
    | ~ iLEQ(suc(B_81),suc(B_82)) ) ).

cnf(clause_418,axiom,
    ( ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(A_3))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_721,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_367,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s('0'),f(suc(suc(B_70))))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_69),f(suc(B_69))) ) ).

cnf(clause_715,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s('0'),f(suc(suc(B_70))))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_1415,axiom,
    ( ~ 'LE'(f(B_67),s(s('0')))
    | 'E'(s('0'),f(B_67))
    | 'LE'(f(B_67),s('0')) ) ).

cnf(clause_1130,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_44),f(suc(B_44)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_44))))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(B_43))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_43),f(suc(B_43))) ) ).

cnf(clause_692,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_80))))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(B_81),f(suc(B_81)))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

cnf(clause_1472,axiom,
    ( ~ 'LE'(f(suc(suc(B_67))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_67))))
    | 'LE'(f(B_67),s('0')) ) ).

cnf(clause_225,axiom,
    ( ~ 'LE'(f(suc(suc(B_79))),s('0'))
    | 'E'('0',f(suc(suc(B_79))))
    | 'LE'(f(B_79),'0') ) ).

cnf(clause_855,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_70))))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68))) ) ).

cnf(clause_639,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_44),f(suc(B_44)))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_44))))
    | ~ 'E'(s(s('0')),f(B_43))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_165,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_709,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_772,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_44),f(suc(B_44)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_44))))
    | ~ 'E'(s(s('0')),f(B_43))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_43),f(suc(B_43)))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_874,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_80))))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ 'E'('0',f(suc(suc(B_81))))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

cnf(clause_1183,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_80))))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ 'E'('0',f(suc(suc(B_81))))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_382,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_80))))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_81),f(suc(B_81))) ) ).

cnf(clause_120,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_243,axiom,
    ( ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_71,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(B_43))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_44),f(suc(B_44))) ) ).

cnf(clause_1246,axiom,
    ( ~ 'LE'(f(suc(B_67)),s(s('0')))
    | 'E'(s('0'),f(suc(B_67)))
    | 'LE'(f(B_67),s('0')) ) ).

cnf(clause_35,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ 'E'('0',f(suc(suc(B_81))))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

cnf(clause_1322,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'(f(B_69),f(suc(B_69)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_332,axiom,
    ( ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_1439,axiom,
    ( ~ 'LE'(f(suc(B_42)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_42)))
    | 'LE'(f(B_42),s(s('0'))) ) ).

cnf(clause_1017,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_44),f(suc(B_44)))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_44))))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1)))) ) ).

cnf(clause_1374,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'(f(B_81),f(suc(B_81))) ) ).

cnf(clause_44,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_987,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | 'E'(f(B_44),f(suc(B_44))) ) ).

cnf(clause_1256,axiom,
    ( ~ 'LE'(f(suc(B_79)),s('0'))
    | 'E'('0',f(suc(B_79)))
    | 'LE'(f(B_79),'0') ) ).

cnf(clause_712,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ 'E'('0',f(suc(suc(B_81))))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80))) ) ).

cnf(clause_354,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(B_43))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_43),f(suc(B_43)))
    | 'E'(f(B_44),f(suc(B_44))) ) ).

cnf(clause_601,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_596,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s('0'),f(suc(suc(B_70))))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_69),f(suc(B_69))) ) ).

cnf(clause_1143,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | 'E'(f(B_43),f(suc(B_43)))
    | 'E'(f(B_44),f(suc(B_44))) ) ).

cnf(clause_460,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_80))))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_81),f(suc(B_81)))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

cnf(clause_1442,axiom,
    ( ~ 'LE'(f(B_42),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_42))
    | 'LE'(f(B_42),s(s('0'))) ) ).

cnf(clause_1365,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_70))))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_68),f(suc(B_68))) ) ).

cnf(clause_1106,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(B_43))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_43),f(suc(B_43)))
    | 'E'(f(B_44),f(suc(B_44)))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_69,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_80))))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(B_81),f(suc(B_81))) ) ).

cnf(clause_1142,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_44),f(suc(B_44)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_44))))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | 'E'(f(B_43),f(suc(B_43)))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_752,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_44),f(suc(B_44)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_44))))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | 'E'(f(B_43),f(suc(B_43))) ) ).

cnf(clause_292,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(B_44))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_43))
    | ~ 'E'(f(B_44),f(suc(B_44)))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ iLEQ(suc(B_44),suc(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(suc(B_44)))
    | ~ iLEQ(suc(B_43),suc(B_44))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s(s('0')),f(suc(suc(B_44))))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(B_43))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_1445,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_70))))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'(f(B_69),f(suc(B_69))) ) ).

cnf(clause_530,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_80))))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ 'E'('0',f(suc(suc(B_81))))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

cnf(clause_129,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_70))))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'(f(B_69),f(suc(B_69))) ) ).

cnf(clause_1132,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s('0'),f(suc(suc(B_70))))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2)) ) ).

cnf(clause_1270,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_509,axiom,
    ( ~ 'LE'(f(B_79),s('0'))
    | 'E'('0',f(B_79))
    | 'LE'(f(B_79),'0') ) ).

cnf(clause_1302,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_70)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_70))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'(f(B_69),f(suc(B_69)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_1261,axiom,
    ( ~ 'LE'(f(suc(suc(B_42))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_42))))
    | 'LE'(f(B_42),s(s('0'))) ) ).

cnf(clause_666,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'('0',f(B_80))
    | ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'('0',f(suc(B_81)))
    | ~ 'E'('0',f(B_81))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_80)))
    | ~ 'E'('0',f(suc(suc(B_81))))
    | ~ iLEQ(suc(B_81),suc(B_82))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

%------------------------------------------------------------------------------
