import RequestProject.TwoAdic.ArcData.A0
import RequestProject.TwoAdic.ArcData.A1
import RequestProject.TwoAdic.ArcData.A2
import RequestProject.TwoAdic.ArcData.A3
import RequestProject.TwoAdic.ArcData.A4
import RequestProject.TwoAdic.ArcData.A5
import RequestProject.TwoAdic.ArcData.A6
import RequestProject.TwoAdic.ArcData.A7
import RequestProject.TwoAdic.ArcData.A8
import RequestProject.TwoAdic.ArcData.A9
import RequestProject.TwoAdic.ArcData.A10
import RequestProject.TwoAdic.ArcData.A11
import RequestProject.TwoAdic.ArcData.A12
import RequestProject.TwoAdic.ArcData.A13
import RequestProject.TwoAdic.ArcData.A14
import RequestProject.TwoAdic.ArcData.A15
import RequestProject.TwoAdic.ArcData.A16
import RequestProject.TwoAdic.ArcData.A17
import RequestProject.TwoAdic.ArcData.A18
import RequestProject.TwoAdic.ArcData.A19
import RequestProject.TwoAdic.ArcData.A20
import RequestProject.TwoAdic.ArcData.A21
import RequestProject.TwoAdic.ArcData.A22
import RequestProject.TwoAdic.ArcData.A23
import RequestProject.TwoAdic.ArcData.A24
import RequestProject.TwoAdic.ArcData.A25
import RequestProject.TwoAdic.ArcData.A26
import RequestProject.TwoAdic.ArcData.A27
import RequestProject.TwoAdic.ArcData.A28
import RequestProject.TwoAdic.ArcData.A29
import RequestProject.TwoAdic.ArcData.A30
import RequestProject.TwoAdic.ArcData.A31
import RequestProject.TwoAdic.ArcData.A32
import RequestProject.TwoAdic.ArcData.A33
import RequestProject.TwoAdic.ArcData.A34
import RequestProject.TwoAdic.ArcData.A35
import RequestProject.TwoAdic.ArcData.A36
import RequestProject.TwoAdic.ArcData.A37
import RequestProject.TwoAdic.ArcData.A38
import RequestProject.TwoAdic.ArcData.A39
import RequestProject.TwoAdic.ArcData.A40
import RequestProject.TwoAdic.ArcData.A41
import RequestProject.TwoAdic.ArcData.A42
import RequestProject.TwoAdic.ArcData.A43
import RequestProject.TwoAdic.ArcData.A44
import RequestProject.TwoAdic.ArcData.A45
import RequestProject.TwoAdic.ArcData.A46
import RequestProject.TwoAdic.ArcData.A47
import RequestProject.TwoAdic.ArcData.A48
import RequestProject.TwoAdic.ArcData.A49
import RequestProject.TwoAdic.ArcData.A50
import RequestProject.TwoAdic.ArcData.A51
import RequestProject.TwoAdic.ArcData.A52
import RequestProject.TwoAdic.ArcData.A53
import RequestProject.TwoAdic.ArcData.A54
import RequestProject.TwoAdic.ArcData.A55
import RequestProject.TwoAdic.ArcData.A56
import RequestProject.TwoAdic.ArcData.A57
import RequestProject.TwoAdic.ArcData.A58
import RequestProject.TwoAdic.ArcData.A59
import RequestProject.TwoAdic.ArcData.A60
import RequestProject.TwoAdic.ArcData.A61
import RequestProject.TwoAdic.ArcData.A62
import RequestProject.TwoAdic.ArcData.A63
import RequestProject.TwoAdic.ArcData.A64
import RequestProject.TwoAdic.ArcData.A65
import RequestProject.TwoAdic.ArcData.A66
import RequestProject.TwoAdic.ArcData.A67
import RequestProject.TwoAdic.ArcData.A68
import RequestProject.TwoAdic.ArcData.A69
import RequestProject.TwoAdic.ArcData.A70
import RequestProject.TwoAdic.ArcData.A71
import RequestProject.TwoAdic.ArcData.A72
import RequestProject.TwoAdic.ArcData.A73
import RequestProject.TwoAdic.ArcData.A74
import RequestProject.TwoAdic.ArcData.A75
import RequestProject.TwoAdic.ArcData.A76
import RequestProject.TwoAdic.ArcData.A77
import RequestProject.TwoAdic.ArcData.A78
import RequestProject.TwoAdic.ArcData.A79
import RequestProject.TwoAdic.ArcData.A80
import RequestProject.TwoAdic.ArcData.A81
import RequestProject.TwoAdic.ArcData.A82
import RequestProject.TwoAdic.ArcData.A83
import RequestProject.TwoAdic.ArcData.A84
import RequestProject.TwoAdic.ArcData.A85
import RequestProject.TwoAdic.ArcData.A86
import RequestProject.TwoAdic.ArcData.A87
import RequestProject.TwoAdic.ArcData.A88
import RequestProject.TwoAdic.ArcData.A89
import RequestProject.TwoAdic.ArcData.A90
import RequestProject.TwoAdic.ArcData.A91
import RequestProject.TwoAdic.ArcData.A92
import RequestProject.TwoAdic.ArcData.A93
import RequestProject.TwoAdic.ArcData.A94
import RequestProject.TwoAdic.ArcData.A95
import RequestProject.TwoAdic.ArcData.A96
import RequestProject.TwoAdic.ArcData.A97
import RequestProject.TwoAdic.ArcData.A98
import RequestProject.TwoAdic.ArcData.A99
import RequestProject.TwoAdic.ArcData.A100
import RequestProject.TwoAdic.ArcData.A101
import RequestProject.TwoAdic.ArcData.A102
import RequestProject.TwoAdic.ArcData.A103
import RequestProject.TwoAdic.ArcData.A104
import RequestProject.TwoAdic.ArcData.A105
import RequestProject.TwoAdic.ArcData.A106
import RequestProject.TwoAdic.ArcData.A107
import RequestProject.TwoAdic.ArcData.A108
import RequestProject.TwoAdic.ArcData.A109
import RequestProject.TwoAdic.ArcData.A110
import RequestProject.TwoAdic.ArcData.A111
import RequestProject.TwoAdic.ArcData.A112
import RequestProject.TwoAdic.ArcData.A113
import RequestProject.TwoAdic.ArcData.A114
import RequestProject.TwoAdic.ArcData.A115
import RequestProject.TwoAdic.ArcData.A116
import RequestProject.TwoAdic.ArcData.A117
import RequestProject.TwoAdic.ArcData.A118
import RequestProject.TwoAdic.CertAll

/-!
# All the arcs of the certificate cells

`arcPairs` pairs each of the 119 certificate cells with its arcs (`ArcData/A*.lean`, generated by
`scripts/gen_arcs_two_adic.py` and checked there by `decide +kernel`); `certCells_arcs`: every cell of
`certCells` has arc data passing `cellArcsOK`.
-/

namespace TwoAdicWin.Arc

open Cert Cert.CertData ArcData

/-- The cells with their arcs. -/
def arcPairs : List (CellD × ArcsD) :=
  [(c0, arcs0), (c1, arcs1), (c2, arcs2), (c3, arcs3), (c4, arcs4), (c5, arcs5), (c6, arcs6), (c7, arcs7), (c8, arcs8), (c9, arcs9), (c10, arcs10), (c11, arcs11), (c12, arcs12), (c13, arcs13), (c14, arcs14), (c15, arcs15), (c16, arcs16), (c17, arcs17), (c18, arcs18), (c19, arcs19), (c20, arcs20), (c21, arcs21), (c22, arcs22), (c23, arcs23), (c24, arcs24), (c25, arcs25), (c26, arcs26), (c27, arcs27), (c28, arcs28), (c29, arcs29), (c30, arcs30), (c31, arcs31), (c32, arcs32), (c33, arcs33), (c34, arcs34), (c35, arcs35), (c36, arcs36), (c37, arcs37), (c38, arcs38), (c39, arcs39), (c40, arcs40), (c41, arcs41), (c42, arcs42), (c43, arcs43), (c44, arcs44), (c45, arcs45), (c46, arcs46), (c47, arcs47), (c48, arcs48), (c49, arcs49), (c50, arcs50), (c51, arcs51), (c52, arcs52), (c53, arcs53), (c54, arcs54), (c55, arcs55), (c56, arcs56), (c57, arcs57), (c58, arcs58), (c59, arcs59), (c60, arcs60), (c61, arcs61), (c62, arcs62), (c63, arcs63), (c64, arcs64), (c65, arcs65), (c66, arcs66), (c67, arcs67), (c68, arcs68), (c69, arcs69), (c70, arcs70), (c71, arcs71), (c72, arcs72), (c73, arcs73), (c74, arcs74), (c75, arcs75), (c76, arcs76), (c77, arcs77), (c78, arcs78), (c79, arcs79), (c80, arcs80), (c81, arcs81), (c82, arcs82), (c83, arcs83), (c84, arcs84), (c85, arcs85), (c86, arcs86), (c87, arcs87), (c88, arcs88), (c89, arcs89), (c90, arcs90), (c91, arcs91), (c92, arcs92), (c93, arcs93), (c94, arcs94), (c95, arcs95), (c96, arcs96), (c97, arcs97), (c98, arcs98), (c99, arcs99), (c100, arcs100), (c101, arcs101), (c102, arcs102), (c103, arcs103), (c104, arcs104), (c105, arcs105), (c106, arcs106), (c107, arcs107), (c108, arcs108), (c109, arcs109), (c110, arcs110), (c111, arcs111), (c112, arcs112), (c113, arcs113), (c114, arcs114), (c115, arcs115), (c116, arcs116), (c117, arcs117), (c118, arcs118)]

set_option maxRecDepth 100000 in
theorem arcPairs_fst : arcPairs.map Prod.fst = certCells := rfl

set_option maxRecDepth 100000 in
theorem arcPairs_ok : ∀ p ∈ arcPairs, cellArcsOK p.1 p.2 = true :=
  List.forall_mem_cons.2 ⟨arcs0_ok, List.forall_mem_cons.2 ⟨arcs1_ok, List.forall_mem_cons.2 ⟨arcs2_ok, List.forall_mem_cons.2 ⟨arcs3_ok, List.forall_mem_cons.2 ⟨arcs4_ok, List.forall_mem_cons.2 ⟨arcs5_ok, List.forall_mem_cons.2 ⟨arcs6_ok, List.forall_mem_cons.2 ⟨arcs7_ok, List.forall_mem_cons.2 ⟨arcs8_ok, List.forall_mem_cons.2 ⟨arcs9_ok, List.forall_mem_cons.2 ⟨arcs10_ok, List.forall_mem_cons.2 ⟨arcs11_ok, List.forall_mem_cons.2 ⟨arcs12_ok, List.forall_mem_cons.2 ⟨arcs13_ok, List.forall_mem_cons.2 ⟨arcs14_ok, List.forall_mem_cons.2 ⟨arcs15_ok, List.forall_mem_cons.2 ⟨arcs16_ok, List.forall_mem_cons.2 ⟨arcs17_ok, List.forall_mem_cons.2 ⟨arcs18_ok, List.forall_mem_cons.2 ⟨arcs19_ok, List.forall_mem_cons.2 ⟨arcs20_ok, List.forall_mem_cons.2 ⟨arcs21_ok, List.forall_mem_cons.2 ⟨arcs22_ok, List.forall_mem_cons.2 ⟨arcs23_ok, List.forall_mem_cons.2 ⟨arcs24_ok, List.forall_mem_cons.2 ⟨arcs25_ok, List.forall_mem_cons.2 ⟨arcs26_ok, List.forall_mem_cons.2 ⟨arcs27_ok, List.forall_mem_cons.2 ⟨arcs28_ok, List.forall_mem_cons.2 ⟨arcs29_ok, List.forall_mem_cons.2 ⟨arcs30_ok, List.forall_mem_cons.2 ⟨arcs31_ok, List.forall_mem_cons.2 ⟨arcs32_ok, List.forall_mem_cons.2 ⟨arcs33_ok, List.forall_mem_cons.2 ⟨arcs34_ok, List.forall_mem_cons.2 ⟨arcs35_ok, List.forall_mem_cons.2 ⟨arcs36_ok, List.forall_mem_cons.2 ⟨arcs37_ok, List.forall_mem_cons.2 ⟨arcs38_ok, List.forall_mem_cons.2 ⟨arcs39_ok, List.forall_mem_cons.2 ⟨arcs40_ok, List.forall_mem_cons.2 ⟨arcs41_ok, List.forall_mem_cons.2 ⟨arcs42_ok, List.forall_mem_cons.2 ⟨arcs43_ok, List.forall_mem_cons.2 ⟨arcs44_ok, List.forall_mem_cons.2 ⟨arcs45_ok, List.forall_mem_cons.2 ⟨arcs46_ok, List.forall_mem_cons.2 ⟨arcs47_ok, List.forall_mem_cons.2 ⟨arcs48_ok, List.forall_mem_cons.2 ⟨arcs49_ok, List.forall_mem_cons.2 ⟨arcs50_ok, List.forall_mem_cons.2 ⟨arcs51_ok, List.forall_mem_cons.2 ⟨arcs52_ok, List.forall_mem_cons.2 ⟨arcs53_ok, List.forall_mem_cons.2 ⟨arcs54_ok, List.forall_mem_cons.2 ⟨arcs55_ok, List.forall_mem_cons.2 ⟨arcs56_ok, List.forall_mem_cons.2 ⟨arcs57_ok, List.forall_mem_cons.2 ⟨arcs58_ok, List.forall_mem_cons.2 ⟨arcs59_ok, List.forall_mem_cons.2 ⟨arcs60_ok, List.forall_mem_cons.2 ⟨arcs61_ok, List.forall_mem_cons.2 ⟨arcs62_ok, List.forall_mem_cons.2 ⟨arcs63_ok, List.forall_mem_cons.2 ⟨arcs64_ok, List.forall_mem_cons.2 ⟨arcs65_ok, List.forall_mem_cons.2 ⟨arcs66_ok, List.forall_mem_cons.2 ⟨arcs67_ok, List.forall_mem_cons.2 ⟨arcs68_ok, List.forall_mem_cons.2 ⟨arcs69_ok, List.forall_mem_cons.2 ⟨arcs70_ok, List.forall_mem_cons.2 ⟨arcs71_ok, List.forall_mem_cons.2 ⟨arcs72_ok, List.forall_mem_cons.2 ⟨arcs73_ok, List.forall_mem_cons.2 ⟨arcs74_ok, List.forall_mem_cons.2 ⟨arcs75_ok, List.forall_mem_cons.2 ⟨arcs76_ok, List.forall_mem_cons.2 ⟨arcs77_ok, List.forall_mem_cons.2 ⟨arcs78_ok, List.forall_mem_cons.2 ⟨arcs79_ok, List.forall_mem_cons.2 ⟨arcs80_ok, List.forall_mem_cons.2 ⟨arcs81_ok, List.forall_mem_cons.2 ⟨arcs82_ok, List.forall_mem_cons.2 ⟨arcs83_ok, List.forall_mem_cons.2 ⟨arcs84_ok, List.forall_mem_cons.2 ⟨arcs85_ok, List.forall_mem_cons.2 ⟨arcs86_ok, List.forall_mem_cons.2 ⟨arcs87_ok, List.forall_mem_cons.2 ⟨arcs88_ok, List.forall_mem_cons.2 ⟨arcs89_ok, List.forall_mem_cons.2 ⟨arcs90_ok, List.forall_mem_cons.2 ⟨arcs91_ok, List.forall_mem_cons.2 ⟨arcs92_ok, List.forall_mem_cons.2 ⟨arcs93_ok, List.forall_mem_cons.2 ⟨arcs94_ok, List.forall_mem_cons.2 ⟨arcs95_ok, List.forall_mem_cons.2 ⟨arcs96_ok, List.forall_mem_cons.2 ⟨arcs97_ok, List.forall_mem_cons.2 ⟨arcs98_ok, List.forall_mem_cons.2 ⟨arcs99_ok, List.forall_mem_cons.2 ⟨arcs100_ok, List.forall_mem_cons.2 ⟨arcs101_ok, List.forall_mem_cons.2 ⟨arcs102_ok, List.forall_mem_cons.2 ⟨arcs103_ok, List.forall_mem_cons.2 ⟨arcs104_ok, List.forall_mem_cons.2 ⟨arcs105_ok, List.forall_mem_cons.2 ⟨arcs106_ok, List.forall_mem_cons.2 ⟨arcs107_ok, List.forall_mem_cons.2 ⟨arcs108_ok, List.forall_mem_cons.2 ⟨arcs109_ok, List.forall_mem_cons.2 ⟨arcs110_ok, List.forall_mem_cons.2 ⟨arcs111_ok, List.forall_mem_cons.2 ⟨arcs112_ok, List.forall_mem_cons.2 ⟨arcs113_ok, List.forall_mem_cons.2 ⟨arcs114_ok, List.forall_mem_cons.2 ⟨arcs115_ok, List.forall_mem_cons.2 ⟨arcs116_ok, List.forall_mem_cons.2 ⟨arcs117_ok, List.forall_mem_cons.2 ⟨arcs118_ok, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Every certificate cell has checked arc data. -/
theorem certCells_arcs : ∀ c ∈ certCells, ∃ D : ArcsD, cellArcsOK c D = true := by
  intro c hc
  rw [← arcPairs_fst, List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  exact ⟨p.2, arcPairs_ok p hp⟩

end TwoAdicWin.Arc
