cnf(p1_is_a0_plus_a1_1,negated_conjecture,
    ( ~ p1
    | a0
    | a1 ) ).

cnf(p1_is_a0_plus_a1_2,negated_conjecture,
    ( ~ p1
    | ~ a0
    | ~ a1 ) ).

cnf(p1_is_a0_plus_a1_3,negated_conjecture,
    ( p1
    | a0
    | ~ a1 ) ).

cnf(p1_is_a0_plus_a1_4,negated_conjecture,
    ( p1
    | ~ a0
    | a1 ) ).

%---- p2 = p1 + a2
cnf(p2_is_p1_plus_a2_1,negated_conjecture,
    ( ~ p2
    | p1
    | a2 ) ).

cnf(p2_is_p1_plus_a2_2,negated_conjecture,
    ( ~ p2
    | ~ p1
    | ~ a2 ) ).

cnf(p2_is_p1_plus_a2_3,negated_conjecture,
    ( p2
    | p1
    | ~ a2 ) ).

cnf(p2_is_p1_plus_a2_4,negated_conjecture,
    ( p2
    | ~ p1
    | a2 ) ).

%---- p3 = p2 + a3
cnf(p3_is_p2_plus_a3_1,negated_conjecture,
    ( ~ p3
    | p2
    | a3 ) ).

cnf(p3_is_p2_plus_a3_2,negated_conjecture,
    ( ~ p3
    | ~ p2
    | a3 ) ).

cnf(p3_is_p2_plus_a3_3,negated_conjecture,
    ( p3
    | p2
    | ~ a3 ) ).

cnf(p3_is_p2_plus_a3_4,negated_conjecture,
    ( p3
    | ~ p2
    | a3 ) ).

%---- p4 = p3 + a4
cnf(p4_is_p3_plus_a4_1,negated_conjecture,
    ( ~ p4
    | p3
    | a4 ) ).

cnf(p4_is_p3_plus_a4_2,negated_conjecture,
    ( ~ p4
    | ~ p3
    | a4 ) ).

cnf(p4_is_p3_plus_a4_3,negated_conjecture,
    ( p4
    | p3
    | ~ a4 ) ).

cnf(p4_is_p3_plus_a4_4,negated_conjecture,
    ( p4
    | ~ p3
    | a4 ) ).

%---- p5 = p4 + a5
cnf(p5_is_p4_plus_a5_1,negated_conjecture,
    ( ~ p5
    | p4
    | a5 ) ).

cnf(p5_is_p4_plus_a5_2,negated_conjecture,
    ( ~ p5
    | ~ p4
    | a5 ) ).

cnf(p5_is_p4_plus_a5_3,negated_conjecture,
    ( p5
    | p4
    | ~ a5 ) ).

cnf(p5_is_p4_plus_a5_4,negated_conjecture,
    ( p5
    | ~ p4
    | a5 ) ).

%---- q1 = b0 + b1
cnf(q1_is_b0_plus_b1_1,negated_conjecture,
    ( ~ q1
    | b0
    | b1 ) ).

cnf(q1_is_b0_plus_b1_2,negated_conjecture,
    ( ~ q1
    | ~ b0
    | ~ b1 ) ).

cnf(q1_is_b0_plus_b1_3,negated_conjecture,
    ( q1
    | b0
    | ~ b1 ) ).

cnf(q1_is_b0_plus_b1_4,negated_conjecture,
    ( q1
    | ~ b0
    | b1 ) ).

%---- q2 = q1 + b2
cnf(q2_is_q1_plus_b2_1,negated_conjecture,
    ( ~ q2
    | q1
    | b2 ) ).

cnf(q2_is_q1_plus_b2_2,negated_conjecture,
    ( ~ q2
    | ~ q1
    | ~ b2 ) ).

cnf(q2_is_q1_plus_b2_3,negated_conjecture,
    ( q2
    | q1
    | ~ b2 ) ).

cnf(q2_is_q1_plus_b2_4,negated_conjecture,
    ( q2
    | ~ q1
    | b2 ) ).

%---- q3 = q2 + b3
cnf(q3_is_q2_plus_b3_1,negated_conjecture,
    ( ~ q3
    | q2
    | b3 ) ).

cnf(q3_is_q2_plus_b3_2,negated_conjecture,
    ( ~ q3
    | ~ q2
    | b3 ) ).

cnf(q3_is_q2_plus_b3_3,negated_conjecture,
    ( q3
    | q2
    | ~ b3 ) ).

cnf(q3_is_q2_plus_b3_4,negated_conjecture,
    ( q3
    | ~ q2
    | b3 ) ).

%---- q4 = q3 + b4
cnf(q4_is_q3_plus_b4_1,negated_conjecture,
    ( ~ q4
    | q3
    | b4 ) ).

cnf(q4_is_q3_plus_b4_2,negated_conjecture,
    ( ~ q4
    | ~ q3
    | b4 ) ).

cnf(q4_is_q3_plus_b4_3,negated_conjecture,
    ( q4
    | q3
    | ~ b4 ) ).

cnf(q4_is_q3_plus_b4_4,negated_conjecture,
    ( q4
    | ~ q3
    | b4 ) ).

%---- q5 = q4 + b5
cnf(q5_is_q4_plus_b5_1,negated_conjecture,
    ( ~ q5
    | q4
    | b5 ) ).

cnf(q5_is_q4_plus_b5_2,negated_conjecture,
    ( ~ q5
    | ~ q4
    | b5 ) ).

cnf(q5_is_q4_plus_b5_3,negated_conjecture,
    ( q5
    | q4
    | ~ b5 ) ).

cnf(q5_is_q4_plus_b5_4,negated_conjecture,
    ( q5
    | ~ q4
    | b5 ) ).

%---- a0 =/= b0
cnf(a0_not_b0_1,negated_conjecture,
    ( a0
    | b0 ) ).

cnf(a0_not_b0_2,negated_conjecture,
    ( ~ a0
    | ~ b0 ) ).

%---- a1 = b1
cnf(a1_is_b1_1,negated_conjecture,
    ( a1
    | ~ b1 ) ).

cnf(a1_is_b1_2,negated_conjecture,
    ( ~ a1
    | b1 ) ).

%---- a2 = b2
cnf(a2_is_b2_1,negated_conjecture,
    ( a2
    | ~ b2 ) ).

cnf(a2_is_b2_2,negated_conjecture,
    ( ~ a2
    | b2 ) ).

%---- a3 = b3
cnf(a3_is_b3_1,negated_conjecture,
    ( a3
    | ~ b3 ) ).

cnf(a3_is_b3_2,negated_conjecture,
    ( ~ a3
    | b3 ) ).

%---- a4 = b4
cnf(a4_is_b4_1,negated_conjecture,
    ( a4
    | ~ b4 ) ).

cnf(a4_is_b4_2,negated_conjecture,
    ( ~ a4
    | b4 ) ).

%---- a5 = b5
cnf(a5_is_b5_1,negated_conjecture,
    ( a5
    | ~ b5 ) ).

cnf(a5_is_b5_2,negated_conjecture,
    ( ~ a5
    | b5 ) ).

%---- a0 + ... + an = b1 + ... + bn
cnf(equal_sum_1,negated_conjecture,
    q5 ).

cnf(equal_sum_2,negated_conjecture,
    p5 ).