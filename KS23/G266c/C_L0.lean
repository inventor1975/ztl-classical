import KS23.G266c.L0
import KS23.G266c.C_X0
import KS23.G266c.C_Y0
import KS23.G266c.C_X1
import KS23.G266c.C_Y1
import KS23.G266c.C_X2
import KS23.G266c.C_Y2
import KS23.G266c.C_X3
import KS23.G266c.C_Y3
import KS23.G266c.C_X4
import KS23.G266c.C_Y4
import KS23.G266c.C_X5
import KS23.G266c.C_Y5
import KS23.G266c.C_X6
import KS23.G266c.C_Y6
import KS23.G266c.C_X7
import KS23.G266c.C_Y7
import KS23.G266c.C_X8
import KS23.G266c.C_Y8
namespace KS23.G266c
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def ch_L0 : Chart where
  phi1 := .v0
  phi2 := .v1
  R := [(1, { x := [[1]], y := [], z := [] }),
    (20, { x := [], y := [[1]], z := [] }),
    (23, { x := [], y := [], z := [[1]] }),
    (2, { x := [[], [-2]], y := [[1], [], [-1]], z := [] }),
    (17, { x := [[-1], [], [1]], y := [[], [-2]], z := [] }),
    (5, { x := [[1, 0, -1]], y := [], z := [[0, -2]] }),
    (11, { x := [[0, -2]], y := [], z := [[-1, 0, 1]] }),
    (19, { x := [[0, -2], [], [0, 2]], y := [[], [0, -4]], z := [[-1, 0, 1], [], [1, 0, -1]] }),
    (22, { x := [], y := [[1, 0, -1], [], [-1, 0, 1]], z := [[], [0, -4]] }),
    (3, { x := [[1, 0, -2, 0, 1], [], [-2, 0, 20, 0, -2], [], [1, 0, -2, 0, 1]], y := [[], [0, 0, -8], [], [0, 0, 8]], z := [[0, -2, 0, 2], [], [0, 4, 0, -4], [], [0, -2, 0, 2]] }),
    (15, { x := [[], [0, 2, 0, -2], [], [0, -4, 0, 4], [], [0, 2, 0, -2]], y := [[0, -1, 0, 1], [], [0, 3, 0, -3], [], [0, -3, 0, 3], [], [0, 1, 0, -1]], z := [[], [1, 0, 2, 0, 1], [], [-2, 0, 12, 0, -2], [], [1, 0, 2, 0, 1]] }),
    (16, { x := [[0, 0, -2, 0, 4, 0, -2], [], [0, 0, 2, 0, -36, 0, 2], [], [0, 0, 4, 0, -40, 0, 4], [], [0, 0, -4, 0, 40, 0, -4], [], [0, 0, -2, 0, 36, 0, -2], [], [0, 0, 2, 0, -4, 0, 2]], y := [[], [-1, 0, -4, 0, 10, 0, -4, 0, -1], [], [4, 0, -16, 0, -40, 0, -16, 0, 4], [], [-6, 0, 40, 0, -196, 0, 40, 0, -6], [], [4, 0, -16, 0, -40, 0, -16, 0, 4], [], [-1, 0, -4, 0, 10, 0, -4, 0, -1]], z := [[0, -1, 0, 3, 0, -3, 0, 1], [], [0, 5, 0, -15, 0, 15, 0, -5], [], [0, -10, 0, 30, 0, -30, 0, 10], [], [0, 10, 0, -30, 0, 30, 0, -10], [], [0, -5, 0, 15, 0, -15, 0, 5], [], [0, 1, 0, -3, 0, 3, 0, -1]] }),
    (18, { x := [[-1, 0, 1], [], [2, 0, -2], [], [-1, 0, 1]], y := [[], [-2, 0, 2], [], [2, 0, -2]], z := [[0, 2], [], [0, 4], [], [0, 2]] }),
    (21, { x := [], y := [[], [0, 4]], z := [[1, 0, -1], [], [-1, 0, 1]] }),
    (4, { x := [[], [-2, 0, -4, 0, -2], [], [4, 0, -24, 0, 4], [], [-2, 0, -4, 0, -2]], y := [[1, 0, -2, 0, 1], [], [-3, 0, 6, 0, -3], [], [3, 0, -6, 0, 3], [], [-1, 0, 2, 0, -1]], z := [[], [0, -4, 0, 4], [], [0, 8, 0, -8], [], [0, -4, 0, 4]] }),
    (7, { x := [[], [], [-2, 0, -4, 0, -2], [], [4, 0, -24, 0, 4], [], [-2, 0, -4, 0, -2]], y := [[], [1, 0, 2, 0, 1], [], [-3, 0, 10, 0, -3], [], [3, 0, -10, 0, 3], [], [-1, 0, -2, 0, -1]], z := [[0, 1, 0, -1], [], [], [], [0, -2, 0, 2], [], [], [], [0, 1, 0, -1]] }),
    (9, { x := [[], [1, 0, 1, 0, -1, 0, -1], [], [-3, 0, 13, 0, -13, 0, 3], [], [3, 0, -13, 0, 13, 0, -3], [], [-1, 0, -1, 0, 1, 0, 1]], y := [[0, 0, 2, 0, -2], [], [2, 0, 2, 0, -2, 0, -2], [], [-4, 0, 24, 0, -24, 0, 4], [], [2, 0, 2, 0, -2, 0, -2], [], [0, 0, 2, 0, -2]], z := [[], [0, -2, 0, -4, 0, -2], [], [0, 6, 0, -20, 0, 6], [], [0, -6, 0, 20, 0, -6], [], [0, 2, 0, 4, 0, 2]] }),
    (10, { x := [[0, 0, 2, 0, -4, 0, 2], [], [2, 0, 0, 0, -4, 0, 0, 0, 2], [], [-4, 0, 28, 0, -48, 0, 28, 0, -4], [], [2, 0, 0, 0, -4, 0, 0, 0, 2], [], [0, 0, 2, 0, -4, 0, 2]], y := [[], [-1, 0, -4, 0, -6, 0, -4, 0, -1], [], [3, 0, -4, 0, -14, 0, -4, 0, 3], [], [-3, 0, 4, 0, 14, 0, 4, 0, -3], [], [1, 0, 4, 0, 6, 0, 4, 0, 1]], z := [[0, 0, 0, -4, 0, 4], [], [0, -4, 0, -4, 0, 4, 0, 4], [], [0, 8, 0, -48, 0, 48, 0, -8], [], [0, -4, 0, -4, 0, 4, 0, 4], [], [0, 0, 0, -4, 0, 4]] }),
    (12, { x := [[], [0, -2, 0, -8, 0, 20, 0, -8, 0, -2], [], [0, 8, 0, -32, 0, -80, 0, -32, 0, 8], [], [0, -12, 0, 80, 0, -392, 0, 80, 0, -12], [], [0, 8, 0, -32, 0, -80, 0, -32, 0, 8], [], [0, -2, 0, -8, 0, 20, 0, -8, 0, -2]], y := [[0, 1, 0, 0, 0, -2, 0, 0, 0, 1], [], [0, -5, 0, 16, 0, 42, 0, 16, 0, -5], [], [0, 10, 0, -48, 0, 140, 0, -48, 0, 10], [], [0, -10, 0, 48, 0, -140, 0, 48, 0, -10], [], [0, 5, 0, -16, 0, -42, 0, -16, 0, 5], [], [0, -1, 0, 0, 0, 2, 0, 0, 0, -1]], z := [[], [-1, 0, -3, 0, 14, 0, -14, 0, 3, 0, 1], [], [4, 0, -20, 0, -24, 0, 24, 0, 20, 0, -4], [], [-6, 0, 46, 0, -236, 0, 236, 0, -46, 0, 6], [], [4, 0, -20, 0, -24, 0, 24, 0, 20, 0, -4], [], [-1, 0, -3, 0, 14, 0, -14, 0, 3, 0, 1]] }),
    (13, { x := [[0, -2, 0, 4, 0, -2], [], [0, 10, 0, -20, 0, 10], [], [0, -20, 0, 40, 0, -20], [], [0, 20, 0, -40, 0, 20], [], [0, -10, 0, 20, 0, -10], [], [0, 2, 0, -4, 0, 2]], y := [[], [0, -8, 0, 0, 0, -8], [], [0, 16, 0, -96, 0, 16], [], [0, -16, 0, -64, 0, -16], [], [0, 16, 0, -96, 0, 16], [], [0, -8, 0, 0, 0, -8]], z := [[-1, 0, 3, 0, -3, 0, 1], [], [1, 0, -19, 0, 19, 0, -1], [], [2, 0, -22, 0, 22, 0, -2], [], [-2, 0, 22, 0, -22, 0, 2], [], [-1, 0, 19, 0, -19, 0, 1], [], [1, 0, -3, 0, 3, 0, -1]] }),
    (14, { x := [[-1, 0, 3, 0, -3, 0, 1], [], [4, 0, -28, 0, 28, 0, -4], [], [-6, 0, 50, 0, -50, 0, 6], [], [4, 0, -28, 0, 28, 0, -4], [], [-1, 0, 3, 0, -3, 0, 1]], y := [[], [-2, 0, -2, 0, 2, 0, 2], [], [6, 0, -26, 0, 26, 0, -6], [], [-6, 0, 26, 0, -26, 0, 6], [], [2, 0, 2, 0, -2, 0, -2]], z := [[], [], [0, 8, 0, 16, 0, 8], [], [0, -16, 0, 96, 0, -16], [], [0, 8, 0, 16, 0, 8]] }),
    (6, { x := [[], [0, -1, 0, 3, 0, 15, 0, -53, 0, 53, 0, -15, 0, -3, 0, 1], [], [0, 12, 0, -4, 0, 44, 0, 60, 0, -60, 0, -44, 0, 4, 0, -12], [], [0, -52, 0, 156, 0, 268, 0, 316, 0, -316, 0, -268, 0, -156, 0, 52], [], [0, 116, 0, -636, 0, 1364, 0, 2116, 0, -2116, 0, -1364, 0, 636, 0, -116], [], [0, -150, 0, 962, 0, -3382, 0, 11506, 0, -11506, 0, 3382, 0, -962, 0, 150], [], [0, 116, 0, -636, 0, 1364, 0, 2116, 0, -2116, 0, -1364, 0, 636, 0, -116], [], [0, -52, 0, 156, 0, 268, 0, 316, 0, -316, 0, -268, 0, -156, 0, 52], [], [0, 12, 0, -4, 0, 44, 0, 60, 0, -60, 0, -44, 0, 4, 0, -12], [], [0, -1, 0, 3, 0, 15, 0, -53, 0, 53, 0, -15, 0, -3, 0, 1]], y := [[0, 0, 0, -2, 0, 2, 0, 4, 0, -4, 0, -2, 0, 2], [], [0, -2, 0, 8, 0, -36, 0, -46, 0, 46, 0, 36, 0, -8, 0, 2], [], [0, 14, 0, -66, 0, 6, 0, -426, 0, 426, 0, -6, 0, 66, 0, -14], [], [0, -42, 0, 278, 0, -610, 0, -418, 0, 418, 0, 610, 0, -278, 0, 42], [], [0, 70, 0, -542, 0, 2034, 0, -4522, 0, 4522, 0, -2034, 0, 542, 0, -70], [], [0, -70, 0, 542, 0, -2034, 0, 4522, 0, -4522, 0, 2034, 0, -542, 0, 70], [], [0, 42, 0, -278, 0, 610, 0, 418, 0, -418, 0, -610, 0, 278, 0, -42], [], [0, -14, 0, 66, 0, -6, 0, 426, 0, -426, 0, 6, 0, -66, 0, 14], [], [0, 2, 0, -8, 0, 36, 0, 46, 0, -46, 0, -36, 0, 8, 0, -2], [], [0, 0, 0, 2, 0, -2, 0, -4, 0, 4, 0, 2, 0, -2]], z := [[], [0, 0, 4, 0, 8, 0, -36, 0, 48, 0, -36, 0, 8, 0, 4], [], [2, 0, -8, 0, 72, 0, 136, 0, 108, 0, 136, 0, 72, 0, -8, 0, 2], [], [-12, 0, 64, 0, -16, 0, 320, 0, 312, 0, 320, 0, -16, 0, 64, 0, -12], [], [30, 0, -248, 0, 824, 0, 120, 0, -1964, 0, 120, 0, 824, 0, -248, 0, 30], [], [-40, 0, 376, 0, -1776, 0, 7112, 0, -13392, 0, 7112, 0, -1776, 0, 376, 0, -40], [], [30, 0, -248, 0, 824, 0, 120, 0, -1964, 0, 120, 0, 824, 0, -248, 0, 30], [], [-12, 0, 64, 0, -16, 0, 320, 0, 312, 0, 320, 0, -16, 0, 64, 0, -12], [], [2, 0, -8, 0, 72, 0, 136, 0, 108, 0, 136, 0, 72, 0, -8, 0, 2], [], [0, 0, 4, 0, 8, 0, -36, 0, 48, 0, -36, 0, 8, 0, 4]] }),
    (8, { x := [[0, 0, 0, -2, 0, 4, 0, -2], [], [0, -4, 0, -8, 0, -8, 0, -8, 0, -4], [], [0, 16, 0, -40, 0, -16, 0, -40, 0, 16], [], [0, -28, 0, 136, 0, -184, 0, 136, 0, -28], [], [0, 32, 0, -172, 0, 408, 0, -172, 0, 32], [], [0, -28, 0, 136, 0, -184, 0, 136, 0, -28], [], [0, 16, 0, -40, 0, -16, 0, -40, 0, 16], [], [0, -4, 0, -8, 0, -8, 0, -8, 0, -4], [], [0, 0, 0, -2, 0, 4, 0, -2]], y := [[], [0, 1, 0, 0, 0, -2, 0, 0, 0, 1], [], [0, -7, 0, 0, 0, -50, 0, 0, 0, -7], [], [0, 21, 0, -64, 0, -106, 0, -64, 0, 21], [], [0, -35, 0, 192, 0, -442, 0, 192, 0, -35], [], [0, 35, 0, -192, 0, 442, 0, -192, 0, 35], [], [0, -21, 0, 64, 0, 106, 0, 64, 0, -21], [], [0, 7, 0, 0, 0, 50, 0, 0, 0, 7], [], [0, -1, 0, 0, 0, 2, 0, 0, 0, -1]], z := [[], [], [-1, 0, -7, 0, -6, 0, 6, 0, 7, 0, 1], [], [2, 0, -18, 0, -84, 0, 84, 0, 18, 0, -2], [], [1, 0, 7, 0, -250, 0, 250, 0, -7, 0, -1], [], [-4, 0, 36, 0, -344, 0, 344, 0, -36, 0, 4], [], [1, 0, 7, 0, -250, 0, 250, 0, -7, 0, -1], [], [2, 0, -18, 0, -84, 0, 84, 0, 18, 0, -2], [], [-1, 0, -7, 0, -6, 0, 6, 0, 7, 0, 1]] })]
  f := []
  X0 := ⟨⟨-1, 0⟩, ⟨1, 0⟩⟩
  Y0 := ⟨⟨-1, 0⟩, ⟨1, 0⟩⟩
  masks := [[], [], [3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]]
  toks := [.split, .split, .split, .ext 0, .ext 1, .ext 2, .ext 3, .split, .ext 4, .ext 5, .ext 6, .ext 7, .split, .ext 8, .ext 9, .ext 10, .ext 11, .split, .ext 12, .ext 13, .ext 14, .ext 15, .split, .split, .ext 16, .ext 17, .ext 18, .ext 19, .split, .ext 20, .ext 21, .ext 22, .ext 23, .split, .ext 24, .ext 25, .ext 26, .ext 27, .split, .ext 28, .ext 29, .ext 30, .ext 31, .split, .split, .ext 32, .ext 33, .ext 34, .ext 35, .split, .ext 36, .ext 37, .ext 38, .ext 39, .split, .ext 40, .ext 41, .ext 42, .ext 43, .split, .ext 44, .ext 45, .ext 46, .ext 47, .split, .split, .ext 48, .ext 49, .ext 50, .ext 51, .split, .ext 52, .ext 53, .ext 54, .ext 55, .split, .ext 56, .ext 57, .ext 58, .ext 59, .split, .ext 60, .ext 61, .ext 62, .ext 63]
  sq := [(⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 4⟩), (⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 4⟩), (⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 4⟩), (⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 4⟩), (⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 4⟩), (⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 4⟩), (⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 4⟩), (⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 4⟩), (⟨-1, 0⟩, ⟨1, 0⟩, ⟨1, 4⟩)]
def pcd_L0_0 : Iv × Iv × List Tok := (⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, ⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, [.split, .split, .split, .split, .split, .split, .split, .split, .split, .split, .split, .opn 6, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_0 : (treeChk C0 ch_L0 [] 64 pcd_L0_0.1 pcd_L0_0.2.1 pcd_L0_0.2.2).isSome = true := by decide +kernel
def pcd_L0_1 : Iv × Iv × List Tok := (⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, ⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, [.split, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 30 0])
set_option maxHeartbeats 0 in
theorem pc_L0_1 : (treeChk C0 ch_L0 [] 64 pcd_L0_1.1 pcd_L0_1.2.1 pcd_L0_1.2.2).isSome = true := by decide +kernel
def pcd_L0_2 : Iv × Iv × List Tok := (⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, ⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, [.split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_2 : (treeChk C0 ch_L0 [] 64 pcd_L0_2.1 pcd_L0_2.2.1 pcd_L0_2.2.2).isSome = true := by decide +kernel
def pcd_L0_3 : Iv × Iv × List Tok := (⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, ⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, [.split, .leaf 21 0, .leaf 21 2, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_3 : (treeChk C0 ch_L0 [] 64 pcd_L0_3.1 pcd_L0_3.2.1 pcd_L0_3.2.2).isSome = true := by decide +kernel
def pcd_L0_4 : Iv × Iv × List Tok := (⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, ⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, [.split, .leaf 36 0, .leaf 36 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_4 : (treeChk C0 ch_L0 [] 64 pcd_L0_4.1 pcd_L0_4.2.1 pcd_L0_4.2.2).isSome = true := by decide +kernel
def pcd_L0_5 : Iv × Iv × List Tok := (⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, ⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, [.split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .opn 4, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_5 : (treeChk C0 ch_L0 [] 64 pcd_L0_5.1 pcd_L0_5.2.1 pcd_L0_5.2.2).isSome = true := by decide +kernel
def pcd_L0_6 : Iv × Iv × List Tok := (⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, ⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, [.split, .leaf 21 2, .leaf 21 2, .leaf 21 2, .leaf 21 2])
set_option maxHeartbeats 0 in
theorem pc_L0_6 : (treeChk C0 ch_L0 [] 64 pcd_L0_6.1 pcd_L0_6.2.1 pcd_L0_6.2.2).isSome = true := by decide +kernel
def pcd_L0_7 : Iv × Iv × List Tok := (⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, ⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, [.split, .split, .leaf 36 2, .leaf 36 2, .leaf 21 2, .leaf 29 2, .split, .leaf 29 2, .leaf 21 0, .leaf 29 0, .leaf 21 0, .leaf 21 2, .leaf 21 2])
set_option maxHeartbeats 0 in
theorem pc_L0_7 : (treeChk C0 ch_L0 [] 64 pcd_L0_7.1 pcd_L0_7.2.1 pcd_L0_7.2.2).isSome = true := by decide +kernel
def pcd_L0_8 : Iv × Iv × List Tok := (⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, ⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, [.split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_8 : (treeChk C0 ch_L0 [] 64 pcd_L0_8.1 pcd_L0_8.2.1 pcd_L0_8.2.2).isSome = true := by decide +kernel
def pcd_L0_9 : Iv × Iv × List Tok := (⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, ⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, [.split, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .split, .leaf 29 0, .leaf 21 0, .leaf 29 0, .leaf 29 0, .split, .leaf 21 0, .leaf 21 0, .leaf 29 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_9 : (treeChk C0 ch_L0 [] 64 pcd_L0_9.1 pcd_L0_9.2.1 pcd_L0_9.2.2).isSome = true := by decide +kernel
def pcd_L0_10 : Iv × Iv × List Tok := (⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, ⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, [.split, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 36 0, .split, .leaf 29 0, .leaf 36 0, .split, .leaf 29 0, .leaf 36 0, .split, .leaf 29 0, .leaf 36 0, .split, .leaf 29 0, .leaf 36 0, .split, .leaf 29 0, .leaf 36 0, .split, .leaf 29 0, .leaf 36 0, .split, .leaf 29 0, .leaf 36 0, .opn 5, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_10 : (treeChk C0 ch_L0 [] 64 pcd_L0_10.1 pcd_L0_10.2.1 pcd_L0_10.2.2).isSome = true := by decide +kernel
def pcd_L0_11 : Iv × Iv × List Tok := (⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, ⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, [.split, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_11 : (treeChk C0 ch_L0 [] 64 pcd_L0_11.1 pcd_L0_11.2.1 pcd_L0_11.2.2).isSome = true := by decide +kernel
def pcd_L0_12 : Iv × Iv × List Tok := (⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, ⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, [.split, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 30 2, .leaf 21 2, .split, .leaf 21 0, .leaf 30 2, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_12 : (treeChk C0 ch_L0 [] 64 pcd_L0_12.1 pcd_L0_12.2.1 pcd_L0_12.2.2).isSome = true := by decide +kernel
def pcd_L0_13 : Iv × Iv × List Tok := (⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, ⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, [.split, .leaf 29 2, .leaf 21 2, .leaf 29 2, .leaf 21 2])
set_option maxHeartbeats 0 in
theorem pc_L0_13 : (treeChk C0 ch_L0 [] 64 pcd_L0_13.1 pcd_L0_13.2.1 pcd_L0_13.2.2).isSome = true := by decide +kernel
def pcd_L0_14 : Iv × Iv × List Tok := (⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, ⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, [.split, .split, .leaf 29 0, .leaf 29 0, .leaf 36 0, .leaf 36 0, .split, .leaf 29 0, .leaf 29 0, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_14 : (treeChk C0 ch_L0 [] 64 pcd_L0_14.1 pcd_L0_14.2.1 pcd_L0_14.2.2).isSome = true := by decide +kernel
def pcd_L0_15 : Iv × Iv × List Tok := (⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, ⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, [.split, .leaf 29 2, .split, .leaf 29 0, .leaf 21 0, .leaf 36 0, .leaf 34 0, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .opn 0, .leaf 36 0, .opn 0])
set_option maxHeartbeats 0 in
theorem pc_L0_15 : (treeChk C0 ch_L0 [] 64 pcd_L0_15.1 pcd_L0_15.2.1 pcd_L0_15.2.2).isSome = true := by decide +kernel
def pcd_L0_16 : Iv × Iv × List Tok := (⟨⟨0, 1⟩, ⟨2, 3⟩⟩, ⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, [.split, .split, .split, .split, .split, .split, .split, .split, .split, .split, .split, .opn 4, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_16 : (treeChk C0 ch_L0 [] 64 pcd_L0_16.1 pcd_L0_16.2.1 pcd_L0_16.2.2).isSome = true := by decide +kernel
def pcd_L0_17 : Iv × Iv × List Tok := (⟨⟨2, 3⟩, ⟨2, 2⟩⟩, ⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, [.split, .leaf 36 0, .leaf 36 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_17 : (treeChk C0 ch_L0 [] 64 pcd_L0_17.1 pcd_L0_17.2.1 pcd_L0_17.2.2).isSome = true := by decide +kernel
def pcd_L0_18 : Iv × Iv × List Tok := (⟨⟨0, 1⟩, ⟨2, 3⟩⟩, ⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, [.split, .split, .leaf 21 0, .leaf 29 2, .leaf 21 0, .leaf 29 0, .split, .leaf 36 2, .leaf 36 2, .leaf 29 2, .leaf 21 2, .leaf 21 2, .leaf 21 2])
set_option maxHeartbeats 0 in
theorem pc_L0_18 : (treeChk C0 ch_L0 [] 64 pcd_L0_18.1 pcd_L0_18.2.1 pcd_L0_18.2.2).isSome = true := by decide +kernel
def pcd_L0_19 : Iv × Iv × List Tok := (⟨⟨2, 3⟩, ⟨2, 2⟩⟩, ⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, [.split, .leaf 21 2, .leaf 21 2, .leaf 21 2, .leaf 21 2])
set_option maxHeartbeats 0 in
theorem pc_L0_19 : (treeChk C0 ch_L0 [] 64 pcd_L0_19.1 pcd_L0_19.2.1 pcd_L0_19.2.2).isSome = true := by decide +kernel
def pcd_L0_20 : Iv × Iv × List Tok := (⟨⟨2, 2⟩, ⟨6, 3⟩⟩, ⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, [.split, .leaf 36 0, .leaf 36 0, .leaf 30 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_20 : (treeChk C0 ch_L0 [] 64 pcd_L0_20.1 pcd_L0_20.2.1 pcd_L0_20.2.2).isSome = true := by decide +kernel
def pcd_L0_21 : Iv × Iv × List Tok := (⟨⟨6, 3⟩, ⟨1, 0⟩⟩, ⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, [.split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .opn 7, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_21 : (treeChk C0 ch_L0 [] 64 pcd_L0_21.1 pcd_L0_21.2.1 pcd_L0_21.2.2).isSome = true := by decide +kernel
def pcd_L0_22 : Iv × Iv × List Tok := (⟨⟨2, 2⟩, ⟨6, 3⟩⟩, ⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, [.split, .leaf 21 2, .leaf 21 0, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_22 : (treeChk C0 ch_L0 [] 64 pcd_L0_22.1 pcd_L0_22.2.1 pcd_L0_22.2.2).isSome = true := by decide +kernel
def pcd_L0_23 : Iv × Iv × List Tok := (⟨⟨6, 3⟩, ⟨1, 0⟩⟩, ⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, [.split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_23 : (treeChk C0 ch_L0 [] 64 pcd_L0_23.1 pcd_L0_23.2.1 pcd_L0_23.2.2).isSome = true := by decide +kernel
def pcd_L0_24 : Iv × Iv × List Tok := (⟨⟨0, 1⟩, ⟨2, 3⟩⟩, ⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, [.split, .leaf 21 2, .leaf 29 2, .leaf 21 2, .leaf 29 2])
set_option maxHeartbeats 0 in
theorem pc_L0_24 : (treeChk C0 ch_L0 [] 64 pcd_L0_24.1 pcd_L0_24.2.1 pcd_L0_24.2.2).isSome = true := by decide +kernel
def pcd_L0_25 : Iv × Iv × List Tok := (⟨⟨2, 3⟩, ⟨2, 2⟩⟩, ⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, [.split, .leaf 21 2, .split, .leaf 21 0, .leaf 21 0, .leaf 30 2, .leaf 21 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 30 2, .leaf 21 0, .leaf 29 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_25 : (treeChk C0 ch_L0 [] 64 pcd_L0_25.1 pcd_L0_25.2.1 pcd_L0_25.2.2).isSome = true := by decide +kernel
def pcd_L0_26 : Iv × Iv × List Tok := (⟨⟨0, 1⟩, ⟨2, 3⟩⟩, ⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, [.split, .split, .leaf 21 0, .leaf 29 0, .leaf 34 0, .leaf 36 0, .leaf 29 2, .split, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .split, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .split, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .split, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .split, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .split, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .split, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .split, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .split, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .split, .opn 0, .leaf 36 0, .opn 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_26 : (treeChk C0 ch_L0 [] 64 pcd_L0_26.1 pcd_L0_26.2.1 pcd_L0_26.2.2).isSome = true := by decide +kernel
def pcd_L0_27 : Iv × Iv × List Tok := (⟨⟨2, 3⟩, ⟨2, 2⟩⟩, ⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, [.split, .split, .leaf 29 0, .leaf 29 0, .leaf 36 0, .leaf 36 0, .split, .leaf 29 0, .leaf 29 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_27 : (treeChk C0 ch_L0 [] 64 pcd_L0_27.1 pcd_L0_27.2.1 pcd_L0_27.2.2).isSome = true := by decide +kernel
def pcd_L0_28 : Iv × Iv × List Tok := (⟨⟨2, 2⟩, ⟨6, 3⟩⟩, ⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, [.split, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .split, .leaf 21 0, .leaf 21 0, .leaf 29 0, .leaf 29 0, .split, .leaf 21 0, .leaf 29 0, .leaf 29 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_28 : (treeChk C0 ch_L0 [] 64 pcd_L0_28.1 pcd_L0_28.2.1 pcd_L0_28.2.2).isSome = true := by decide +kernel
def pcd_L0_29 : Iv × Iv × List Tok := (⟨⟨6, 3⟩, ⟨1, 0⟩⟩, ⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, [.split, .leaf 21 0, .leaf 21 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_29 : (treeChk C0 ch_L0 [] 64 pcd_L0_29.1 pcd_L0_29.2.1 pcd_L0_29.2.2).isSome = true := by decide +kernel
def pcd_L0_30 : Iv × Iv × List Tok := (⟨⟨2, 2⟩, ⟨6, 3⟩⟩, ⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, [.split, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_30 : (treeChk C0 ch_L0 [] 64 pcd_L0_30.1 pcd_L0_30.2.1 pcd_L0_30.2.2).isSome = true := by decide +kernel
def pcd_L0_31 : Iv × Iv × List Tok := (⟨⟨6, 3⟩, ⟨1, 0⟩⟩, ⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, [.split, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .split, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 36 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 36 0, .leaf 29 0, .leaf 29 0, .split, .leaf 36 0, .leaf 29 0, .leaf 36 0, .split, .leaf 36 0, .leaf 29 0, .leaf 36 0, .split, .leaf 36 0, .leaf 29 0, .leaf 36 0, .split, .leaf 36 0, .leaf 29 0, .leaf 36 0, .split, .leaf 36 0, .leaf 29 0, .leaf 36 0, .split, .leaf 36 0, .leaf 29 0, .leaf 36 0, .split, .leaf 36 0, .leaf 29 0, .leaf 36 0, .opn 2])
set_option maxHeartbeats 0 in
theorem pc_L0_31 : (treeChk C0 ch_L0 [] 64 pcd_L0_31.1 pcd_L0_31.2.1 pcd_L0_31.2.2).isSome = true := by decide +kernel
def pcd_L0_32 : Iv × Iv × List Tok := (⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, ⟨⟨0, 1⟩, ⟨2, 3⟩⟩, [.split, .split, .split, .split, .split, .split, .split, .split, .split, .split, .split, .opn 5, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 36 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_32 : (treeChk C0 ch_L0 [] 64 pcd_L0_32.1 pcd_L0_32.2.1 pcd_L0_32.2.2).isSome = true := by decide +kernel
def pcd_L0_33 : Iv × Iv × List Tok := (⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, ⟨⟨0, 1⟩, ⟨2, 3⟩⟩, [.split, .split, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_33 : (treeChk C0 ch_L0 [] 64 pcd_L0_33.1 pcd_L0_33.2.1 pcd_L0_33.2.2).isSome = true := by decide +kernel
def pcd_L0_34 : Iv × Iv × List Tok := (⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, ⟨⟨2, 3⟩, ⟨2, 2⟩⟩, [.split, .leaf 21 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_34 : (treeChk C0 ch_L0 [] 64 pcd_L0_34.1 pcd_L0_34.2.1 pcd_L0_34.2.2).isSome = true := by decide +kernel
def pcd_L0_35 : Iv × Iv × List Tok := (⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, ⟨⟨2, 3⟩, ⟨2, 2⟩⟩, [.split, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 21 0, .split, .leaf 29 0, .leaf 29 0, .leaf 21 0, .leaf 21 0, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_35 : (treeChk C0 ch_L0 [] 64 pcd_L0_35.1 pcd_L0_35.2.1 pcd_L0_35.2.2).isSome = true := by decide +kernel
def pcd_L0_36 : Iv × Iv × List Tok := (⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, ⟨⟨0, 1⟩, ⟨2, 3⟩⟩, [.split, .leaf 29 0, .leaf 36 0, .split, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 29 0, .split, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_36 : (treeChk C0 ch_L0 [] 64 pcd_L0_36.1 pcd_L0_36.2.1 pcd_L0_36.2.2).isSome = true := by decide +kernel
def pcd_L0_37 : Iv × Iv × List Tok := (⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, ⟨⟨0, 1⟩, ⟨2, 3⟩⟩, [.split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .opn 0, .leaf 36 0, .opn 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 29 2, .split, .leaf 36 0, .leaf 34 0, .leaf 29 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_37 : (treeChk C0 ch_L0 [] 64 pcd_L0_37.1 pcd_L0_37.2.1 pcd_L0_37.2.2).isSome = true := by decide +kernel
def pcd_L0_38 : Iv × Iv × List Tok := (⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, ⟨⟨2, 3⟩, ⟨2, 2⟩⟩, [.split, .split, .leaf 29 0, .leaf 29 0, .leaf 21 0, .leaf 30 2, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 21 0, .leaf 30 2, .leaf 21 0, .leaf 21 0, .leaf 21 2])
set_option maxHeartbeats 0 in
theorem pc_L0_38 : (treeChk C0 ch_L0 [] 64 pcd_L0_38.1 pcd_L0_38.2.1 pcd_L0_38.2.2).isSome = true := by decide +kernel
def pcd_L0_39 : Iv × Iv × List Tok := (⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, ⟨⟨2, 3⟩, ⟨2, 2⟩⟩, [.split, .leaf 29 2, .leaf 21 2, .leaf 29 2, .leaf 21 2])
set_option maxHeartbeats 0 in
theorem pc_L0_39 : (treeChk C0 ch_L0 [] 64 pcd_L0_39.1 pcd_L0_39.2.1 pcd_L0_39.2.2).isSome = true := by decide +kernel
def pcd_L0_40 : Iv × Iv × List Tok := (⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, ⟨⟨2, 2⟩, ⟨6, 3⟩⟩, [.split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_40 : (treeChk C0 ch_L0 [] 64 pcd_L0_40.1 pcd_L0_40.2.1 pcd_L0_40.2.2).isSome = true := by decide +kernel
def pcd_L0_41 : Iv × Iv × List Tok := (⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, ⟨⟨2, 2⟩, ⟨6, 3⟩⟩, [.split, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 2])
set_option maxHeartbeats 0 in
theorem pc_L0_41 : (treeChk C0 ch_L0 [] 64 pcd_L0_41.1 pcd_L0_41.2.1 pcd_L0_41.2.2).isSome = true := by decide +kernel
def pcd_L0_42 : Iv × Iv × List Tok := (⟨⟨-1, 0⟩, ⟨-6, 3⟩⟩, ⟨⟨6, 3⟩, ⟨1, 0⟩⟩, [.split, .leaf 21 0, .leaf 21 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .opn 8, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_42 : (treeChk C0 ch_L0 [] 64 pcd_L0_42.1 pcd_L0_42.2.1 pcd_L0_42.2.2).isSome = true := by decide +kernel
def pcd_L0_43 : Iv × Iv × List Tok := (⟨⟨-6, 3⟩, ⟨-2, 2⟩⟩, ⟨⟨6, 3⟩, ⟨1, 0⟩⟩, [.split, .leaf 21 0, .leaf 30 0, .leaf 36 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_43 : (treeChk C0 ch_L0 [] 64 pcd_L0_43.1 pcd_L0_43.2.1 pcd_L0_43.2.2).isSome = true := by decide +kernel
def pcd_L0_44 : Iv × Iv × List Tok := (⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, ⟨⟨2, 2⟩, ⟨6, 3⟩⟩, [.split, .leaf 21 2, .leaf 21 2, .leaf 21 2, .leaf 21 2])
set_option maxHeartbeats 0 in
theorem pc_L0_44 : (treeChk C0 ch_L0 [] 64 pcd_L0_44.1 pcd_L0_44.2.1 pcd_L0_44.2.2).isSome = true := by decide +kernel
def pcd_L0_45 : Iv × Iv × List Tok := (⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, ⟨⟨2, 2⟩, ⟨6, 3⟩⟩, [.split, .leaf 21 2, .leaf 21 2, .split, .leaf 21 2, .leaf 29 2, .leaf 36 2, .leaf 36 2, .split, .leaf 29 0, .leaf 21 0, .leaf 29 2, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_45 : (treeChk C0 ch_L0 [] 64 pcd_L0_45.1 pcd_L0_45.2.1 pcd_L0_45.2.2).isSome = true := by decide +kernel
def pcd_L0_46 : Iv × Iv × List Tok := (⟨⟨-2, 2⟩, ⟨-2, 3⟩⟩, ⟨⟨6, 3⟩, ⟨1, 0⟩⟩, [.split, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_46 : (treeChk C0 ch_L0 [] 64 pcd_L0_46.1 pcd_L0_46.2.1 pcd_L0_46.2.2).isSome = true := by decide +kernel
def pcd_L0_47 : Iv × Iv × List Tok := (⟨⟨-2, 3⟩, ⟨0, 1⟩⟩, ⟨⟨6, 3⟩, ⟨1, 0⟩⟩, [.split, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .opn 1])
set_option maxHeartbeats 0 in
theorem pc_L0_47 : (treeChk C0 ch_L0 [] 64 pcd_L0_47.1 pcd_L0_47.2.1 pcd_L0_47.2.2).isSome = true := by decide +kernel
def pcd_L0_48 : Iv × Iv × List Tok := (⟨⟨0, 1⟩, ⟨2, 3⟩⟩, ⟨⟨0, 1⟩, ⟨2, 3⟩⟩, [.split, .split, .split, .split, .split, .split, .split, .split, .split, .split, .split, .opn 0, .leaf 36 0, .opn 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 34 0, .leaf 36 0, .leaf 21 0, .leaf 29 0, .leaf 29 2])
set_option maxHeartbeats 0 in
theorem pc_L0_48 : (treeChk C0 ch_L0 [] 64 pcd_L0_48.1 pcd_L0_48.2.1 pcd_L0_48.2.2).isSome = true := by decide +kernel
def pcd_L0_49 : Iv × Iv × List Tok := (⟨⟨2, 3⟩, ⟨2, 2⟩⟩, ⟨⟨0, 1⟩, ⟨2, 3⟩⟩, [.split, .leaf 36 0, .leaf 29 0, .split, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 29 0, .split, .leaf 36 0, .leaf 36 0, .leaf 29 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_49 : (treeChk C0 ch_L0 [] 64 pcd_L0_49.1 pcd_L0_49.2.1 pcd_L0_49.2.2).isSome = true := by decide +kernel
def pcd_L0_50 : Iv × Iv × List Tok := (⟨⟨0, 1⟩, ⟨2, 3⟩⟩, ⟨⟨2, 3⟩, ⟨2, 2⟩⟩, [.split, .leaf 21 2, .leaf 29 2, .leaf 21 2, .leaf 29 2])
set_option maxHeartbeats 0 in
theorem pc_L0_50 : (treeChk C0 ch_L0 [] 64 pcd_L0_50.1 pcd_L0_50.2.1 pcd_L0_50.2.2).isSome = true := by decide +kernel
def pcd_L0_51 : Iv × Iv × List Tok := (⟨⟨2, 3⟩, ⟨2, 2⟩⟩, ⟨⟨2, 3⟩, ⟨2, 2⟩⟩, [.split, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 30 2, .leaf 21 0, .leaf 21 2, .split, .leaf 30 2, .leaf 21 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_51 : (treeChk C0 ch_L0 [] 64 pcd_L0_51.1 pcd_L0_51.2.1 pcd_L0_51.2.2).isSome = true := by decide +kernel
def pcd_L0_52 : Iv × Iv × List Tok := (⟨⟨2, 2⟩, ⟨6, 3⟩⟩, ⟨⟨0, 1⟩, ⟨2, 3⟩⟩, [.split, .leaf 29 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_52 : (treeChk C0 ch_L0 [] 64 pcd_L0_52.1 pcd_L0_52.2.1 pcd_L0_52.2.2).isSome = true := by decide +kernel
def pcd_L0_53 : Iv × Iv × List Tok := (⟨⟨6, 3⟩, ⟨1, 0⟩⟩, ⟨⟨0, 1⟩, ⟨2, 3⟩⟩, [.split, .split, .leaf 36 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 29 0, .split, .leaf 29 0, .split, .leaf 29 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .split, .leaf 36 0, .opn 2, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .leaf 36 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0])
set_option maxHeartbeats 0 in
theorem pc_L0_53 : (treeChk C0 ch_L0 [] 64 pcd_L0_53.1 pcd_L0_53.2.1 pcd_L0_53.2.2).isSome = true := by decide +kernel
def pcd_L0_54 : Iv × Iv × List Tok := (⟨⟨2, 2⟩, ⟨6, 3⟩⟩, ⟨⟨2, 3⟩, ⟨2, 2⟩⟩, [.split, .split, .leaf 29 0, .leaf 29 0, .leaf 21 0, .leaf 21 0, .split, .leaf 29 0, .leaf 29 0, .leaf 21 0, .leaf 29 0, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_54 : (treeChk C0 ch_L0 [] 64 pcd_L0_54.1 pcd_L0_54.2.1 pcd_L0_54.2.2).isSome = true := by decide +kernel
def pcd_L0_55 : Iv × Iv × List Tok := (⟨⟨6, 3⟩, ⟨1, 0⟩⟩, ⟨⟨2, 3⟩, ⟨2, 2⟩⟩, [.split, .split, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 29 0, .leaf 21 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_55 : (treeChk C0 ch_L0 [] 64 pcd_L0_55.1 pcd_L0_55.2.1 pcd_L0_55.2.2).isSome = true := by decide +kernel
def pcd_L0_56 : Iv × Iv × List Tok := (⟨⟨0, 1⟩, ⟨2, 3⟩⟩, ⟨⟨2, 2⟩, ⟨6, 3⟩⟩, [.split, .leaf 21 2, .leaf 21 2, .split, .leaf 21 0, .leaf 29 0, .leaf 21 0, .leaf 29 2, .split, .leaf 29 2, .leaf 21 2, .leaf 36 2, .leaf 36 2])
set_option maxHeartbeats 0 in
theorem pc_L0_56 : (treeChk C0 ch_L0 [] 64 pcd_L0_56.1 pcd_L0_56.2.1 pcd_L0_56.2.2).isSome = true := by decide +kernel
def pcd_L0_57 : Iv × Iv × List Tok := (⟨⟨2, 3⟩, ⟨2, 2⟩⟩, ⟨⟨2, 2⟩, ⟨6, 3⟩⟩, [.split, .leaf 21 2, .leaf 21 2, .leaf 21 2, .leaf 21 2])
set_option maxHeartbeats 0 in
theorem pc_L0_57 : (treeChk C0 ch_L0 [] 64 pcd_L0_57.1 pcd_L0_57.2.1 pcd_L0_57.2.2).isSome = true := by decide +kernel
def pcd_L0_58 : Iv × Iv × List Tok := (⟨⟨0, 1⟩, ⟨2, 3⟩⟩, ⟨⟨6, 3⟩, ⟨1, 0⟩⟩, [.split, .split, .leaf 21 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .split, .leaf 21 0, .leaf 36 0, .leaf 21 0, .leaf 36 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .split, .leaf 21 0, .leaf 36 0, .opn 1, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_58 : (treeChk C0 ch_L0 [] 64 pcd_L0_58.1 pcd_L0_58.2.1 pcd_L0_58.2.2).isSome = true := by decide +kernel
def pcd_L0_59 : Iv × Iv × List Tok := (⟨⟨2, 3⟩, ⟨2, 2⟩⟩, ⟨⟨6, 3⟩, ⟨1, 0⟩⟩, [.split, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .split, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_59 : (treeChk C0 ch_L0 [] 64 pcd_L0_59.1 pcd_L0_59.2.1 pcd_L0_59.2.2).isSome = true := by decide +kernel
def pcd_L0_60 : Iv × Iv × List Tok := (⟨⟨2, 2⟩, ⟨6, 3⟩⟩, ⟨⟨2, 2⟩, ⟨6, 3⟩⟩, [.split, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 2, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_60 : (treeChk C0 ch_L0 [] 64 pcd_L0_60.1 pcd_L0_60.2.1 pcd_L0_60.2.2).isSome = true := by decide +kernel
def pcd_L0_61 : Iv × Iv × List Tok := (⟨⟨6, 3⟩, ⟨1, 0⟩⟩, ⟨⟨2, 2⟩, ⟨6, 3⟩⟩, [.split, .leaf 21 0, .leaf 21 0, .leaf 21 0, .leaf 21 0])
set_option maxHeartbeats 0 in
theorem pc_L0_61 : (treeChk C0 ch_L0 [] 64 pcd_L0_61.1 pcd_L0_61.2.1 pcd_L0_61.2.2).isSome = true := by decide +kernel
def pcd_L0_62 : Iv × Iv × List Tok := (⟨⟨2, 2⟩, ⟨6, 3⟩⟩, ⟨⟨6, 3⟩, ⟨1, 0⟩⟩, [.split, .leaf 30 0, .leaf 21 0, .leaf 36 0, .leaf 36 0])
set_option maxHeartbeats 0 in
theorem pc_L0_62 : (treeChk C0 ch_L0 [] 64 pcd_L0_62.1 pcd_L0_62.2.1 pcd_L0_62.2.2).isSome = true := by decide +kernel
def pcd_L0_63 : Iv × Iv × List Tok := (⟨⟨6, 3⟩, ⟨1, 0⟩⟩, ⟨⟨6, 3⟩, ⟨1, 0⟩⟩, [.split, .leaf 21 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .split, .leaf 36 0, .leaf 21 0, .leaf 36 0, .opn 3])
set_option maxHeartbeats 0 in
theorem pc_L0_63 : (treeChk C0 ch_L0 [] 64 pcd_L0_63.1 pcd_L0_63.2.1 pcd_L0_63.2.2).isSome = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_L0 : chartChk C0 ch_L0 [pcd_L0_0, pcd_L0_1, pcd_L0_2, pcd_L0_3, pcd_L0_4, pcd_L0_5, pcd_L0_6, pcd_L0_7, pcd_L0_8, pcd_L0_9, pcd_L0_10, pcd_L0_11, pcd_L0_12, pcd_L0_13, pcd_L0_14, pcd_L0_15, pcd_L0_16, pcd_L0_17, pcd_L0_18, pcd_L0_19, pcd_L0_20, pcd_L0_21, pcd_L0_22, pcd_L0_23, pcd_L0_24, pcd_L0_25, pcd_L0_26, pcd_L0_27, pcd_L0_28, pcd_L0_29, pcd_L0_30, pcd_L0_31, pcd_L0_32, pcd_L0_33, pcd_L0_34, pcd_L0_35, pcd_L0_36, pcd_L0_37, pcd_L0_38, pcd_L0_39, pcd_L0_40, pcd_L0_41, pcd_L0_42, pcd_L0_43, pcd_L0_44, pcd_L0_45, pcd_L0_46, pcd_L0_47, pcd_L0_48, pcd_L0_49, pcd_L0_50, pcd_L0_51, pcd_L0_52, pcd_L0_53, pcd_L0_54, pcd_L0_55, pcd_L0_56, pcd_L0_57, pcd_L0_58, pcd_L0_59, pcd_L0_60, pcd_L0_61, pcd_L0_62, pcd_L0_63] [(ch_X0, ch_Y0), (ch_X1, ch_Y1), (ch_X2, ch_Y2), (ch_X3, ch_Y3), (ch_X4, ch_Y4), (ch_X5, ch_Y5), (ch_X6, ch_Y6), (ch_X7, ch_Y7), (ch_X8, ch_Y8)] = true := by decide +kernel
theorem ok_L0 : ChartOK C0 ch_L0 := chart_ok C0 hC0 ch_L0 [pcd_L0_0, pcd_L0_1, pcd_L0_2, pcd_L0_3, pcd_L0_4, pcd_L0_5, pcd_L0_6, pcd_L0_7, pcd_L0_8, pcd_L0_9, pcd_L0_10, pcd_L0_11, pcd_L0_12, pcd_L0_13, pcd_L0_14, pcd_L0_15, pcd_L0_16, pcd_L0_17, pcd_L0_18, pcd_L0_19, pcd_L0_20, pcd_L0_21, pcd_L0_22, pcd_L0_23, pcd_L0_24, pcd_L0_25, pcd_L0_26, pcd_L0_27, pcd_L0_28, pcd_L0_29, pcd_L0_30, pcd_L0_31, pcd_L0_32, pcd_L0_33, pcd_L0_34, pcd_L0_35, pcd_L0_36, pcd_L0_37, pcd_L0_38, pcd_L0_39, pcd_L0_40, pcd_L0_41, pcd_L0_42, pcd_L0_43, pcd_L0_44, pcd_L0_45, pcd_L0_46, pcd_L0_47, pcd_L0_48, pcd_L0_49, pcd_L0_50, pcd_L0_51, pcd_L0_52, pcd_L0_53, pcd_L0_54, pcd_L0_55, pcd_L0_56, pcd_L0_57, pcd_L0_58, pcd_L0_59, pcd_L0_60, pcd_L0_61, pcd_L0_62, pcd_L0_63] [(ch_X0, ch_Y0), (ch_X1, ch_Y1), (ch_X2, ch_Y2), (ch_X3, ch_Y3), (ch_X4, ch_Y4), (ch_X5, ch_Y5), (ch_X6, ch_Y6), (ch_X7, ch_Y7), (ch_X8, ch_Y8)] chk_L0 (List.forall_mem_cons.2 ⟨pc_L0_0, List.forall_mem_cons.2 ⟨pc_L0_1, List.forall_mem_cons.2 ⟨pc_L0_2, List.forall_mem_cons.2 ⟨pc_L0_3, List.forall_mem_cons.2 ⟨pc_L0_4, List.forall_mem_cons.2 ⟨pc_L0_5, List.forall_mem_cons.2 ⟨pc_L0_6, List.forall_mem_cons.2 ⟨pc_L0_7, List.forall_mem_cons.2 ⟨pc_L0_8, List.forall_mem_cons.2 ⟨pc_L0_9, List.forall_mem_cons.2 ⟨pc_L0_10, List.forall_mem_cons.2 ⟨pc_L0_11, List.forall_mem_cons.2 ⟨pc_L0_12, List.forall_mem_cons.2 ⟨pc_L0_13, List.forall_mem_cons.2 ⟨pc_L0_14, List.forall_mem_cons.2 ⟨pc_L0_15, List.forall_mem_cons.2 ⟨pc_L0_16, List.forall_mem_cons.2 ⟨pc_L0_17, List.forall_mem_cons.2 ⟨pc_L0_18, List.forall_mem_cons.2 ⟨pc_L0_19, List.forall_mem_cons.2 ⟨pc_L0_20, List.forall_mem_cons.2 ⟨pc_L0_21, List.forall_mem_cons.2 ⟨pc_L0_22, List.forall_mem_cons.2 ⟨pc_L0_23, List.forall_mem_cons.2 ⟨pc_L0_24, List.forall_mem_cons.2 ⟨pc_L0_25, List.forall_mem_cons.2 ⟨pc_L0_26, List.forall_mem_cons.2 ⟨pc_L0_27, List.forall_mem_cons.2 ⟨pc_L0_28, List.forall_mem_cons.2 ⟨pc_L0_29, List.forall_mem_cons.2 ⟨pc_L0_30, List.forall_mem_cons.2 ⟨pc_L0_31, List.forall_mem_cons.2 ⟨pc_L0_32, List.forall_mem_cons.2 ⟨pc_L0_33, List.forall_mem_cons.2 ⟨pc_L0_34, List.forall_mem_cons.2 ⟨pc_L0_35, List.forall_mem_cons.2 ⟨pc_L0_36, List.forall_mem_cons.2 ⟨pc_L0_37, List.forall_mem_cons.2 ⟨pc_L0_38, List.forall_mem_cons.2 ⟨pc_L0_39, List.forall_mem_cons.2 ⟨pc_L0_40, List.forall_mem_cons.2 ⟨pc_L0_41, List.forall_mem_cons.2 ⟨pc_L0_42, List.forall_mem_cons.2 ⟨pc_L0_43, List.forall_mem_cons.2 ⟨pc_L0_44, List.forall_mem_cons.2 ⟨pc_L0_45, List.forall_mem_cons.2 ⟨pc_L0_46, List.forall_mem_cons.2 ⟨pc_L0_47, List.forall_mem_cons.2 ⟨pc_L0_48, List.forall_mem_cons.2 ⟨pc_L0_49, List.forall_mem_cons.2 ⟨pc_L0_50, List.forall_mem_cons.2 ⟨pc_L0_51, List.forall_mem_cons.2 ⟨pc_L0_52, List.forall_mem_cons.2 ⟨pc_L0_53, List.forall_mem_cons.2 ⟨pc_L0_54, List.forall_mem_cons.2 ⟨pc_L0_55, List.forall_mem_cons.2 ⟨pc_L0_56, List.forall_mem_cons.2 ⟨pc_L0_57, List.forall_mem_cons.2 ⟨pc_L0_58, List.forall_mem_cons.2 ⟨pc_L0_59, List.forall_mem_cons.2 ⟨pc_L0_60, List.forall_mem_cons.2 ⟨pc_L0_61, List.forall_mem_cons.2 ⟨pc_L0_62, List.forall_mem_cons.2 ⟨pc_L0_63, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) (List.forall_mem_cons.2 ⟨⟨ok_X0, ok_Y0⟩, List.forall_mem_cons.2 ⟨⟨ok_X1, ok_Y1⟩, List.forall_mem_cons.2 ⟨⟨ok_X2, ok_Y2⟩, List.forall_mem_cons.2 ⟨⟨ok_X3, ok_Y3⟩, List.forall_mem_cons.2 ⟨⟨ok_X4, ok_Y4⟩, List.forall_mem_cons.2 ⟨⟨ok_X5, ok_Y5⟩, List.forall_mem_cons.2 ⟨⟨ok_X6, ok_Y6⟩, List.forall_mem_cons.2 ⟨⟨ok_X7, ok_Y7⟩, List.forall_mem_cons.2 ⟨⟨ok_X8, ok_Y8⟩, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩)
end KS23.G266c
