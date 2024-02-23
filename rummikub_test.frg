#lang forge/bsl
open "two_player_rummikub.frg"


test suite for wellformed {
  // Fill me in!
}

test suite for drawNewTile {
  // Fill me in!
}

pred tile_run {
  some color1, color2, color3 : Color, value1, value2, value3 : Int | {
    (color1 = color2 and color2 = color3 and 
    consecutiveNumbers[value1, value2, value3])
  }
}

pred tile_group {
  some color1, color2, color3 : Color, value1, value2, value3 : Int | {
    (color1 != color2 and color2 != color3 and color1 != color3 and
    value1 = value2 and value2 = value3)
  }
}

test suite for playableSet {
  // Fill me in!
  // assert tile_run is necessary for playableSet[]
  // assert tile_group is necessary for playableSet
}

test suite for consecutiveNumbers {
  //basic accending / decending / pos / neg tests : SAT
  test expect { is_consec_accenting: {consecutiveNumbers[2, 3, 4]} is sat }  
  test expect { is_consec_accending_negTOpos: {consecutiveNumbers[-1, 0, 1]} is sat } 
  test expect { is_consec_decending: {consecutiveNumbers[15, 14, 13]} is sat }  
  test expect { is_consec_decending_posTOneg: {consecutiveNumbers[1, 0, -1]} is sat } 

  //basic accending / decending / pos / neg tests : UNSAT
  test expect { not_consec_accending: {consecutiveNumbers[2, 3, 5]} is unsat }  
  test expect { not_consec_accending_negTopos: {consecutiveNumbers[-5, 0, 2]} is unsat }  
  test expect { not_consec__decending: {consecutiveNumbers[200, 100, 20]} is unsat }  
  test expect { not_consec_decending_postoneg: {consecutiveNumbers[30, 0, -20]} is unsat }  
  test expect { not_equal: {consecutiveNumbers[0, 0, 0]} is unsat }  

  //v1 < v2 < v3
  test expect { case_1: {consecutiveNumbers[10, 11, 12]} is sat }  
  //v1 < v3 < v2
  test expect { case_2: {consecutiveNumbers[10, 12, 11]} is sat }  
  //v2 < v1 < v3
  test expect { case_3: {consecutiveNumbers[11, 10, 12]} is sat }
  //v2 < v3 < v1
  test expect { case_4: {consecutiveNumbers[12, 10, 11]} is sat }
  //v3 < v1 < v2
  test expect { case_5: {consecutiveNumbers[11, 12, 10]} is sat }
  //v3 < v2 < v1
  test expect { case_6: {consecutiveNumbers[12, 11, 10]} is sat }
}

test suite for canPlayFirstHand {
    // Fill me in!

}

