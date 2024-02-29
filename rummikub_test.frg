#lang forge/bsl
open "two_player_rummikub.frg"

-----------------------------------------INIT------------------------------------------
assert all p: Pool | init[p] is sufficient for aturn[p] 

---------------------------------------WELLFORMED---------------------------------------

pred color_check {
    all p: Pool, color: Color | {
        color = Blue or 
        color = Red or
        color = Yellow or 
        color = Green
    } 
}

pred value_check {
    all p: Pool, color: Color, val: Int | {
            (val < 0) implies
            no p.tiles[color][val]
    } 
}

test suite for wellformed {
  // Fill me in!
  assert color_check is necessary for wellformed
  assert value_check is necessary for wellformed
}

---------------------------------------drawNewTile---------------------------------------

test suite for drawNewTile {
  // Fill me in!
  // assert board_changed is necessary for drawNewTile
  // assert player_cnt_increased is necessary for drawNewTile

  // some tile must be different btwn pre and post board
  test expect {
        dnt_case1: {
          some pre, post: Pool, p: Player, c: Color, v: Int | {
            {
              pre.tiles[c][v] != post.tiles[c][v]
              drawNewTile[pre, post, p, c, v]
            }
        } 
    } is sat 
  }

  //after move the number of player p tiles on pre board should be less that that on the post board 
  test expect {
        dnt_case2: {
            some pre, post: Pool, p: Player, c: Color, v: Int | {
              {
              #{c: Color, v:Int | pre.tiles[c][v] = p} < #{c: Color, v:Int | post.tiles[c][v] = p}
              drawNewTile[pre, post, p, c, v]
              }
          } 
      } is sat 
  }

  //must have placed a new tile 
  test expect {
        dnt_case3: {
            some pre, post: Pool, p: Player, c: Color, v: Int | {
              {
              #{c: Color, v:Int | pre.tiles[c][v] = p} = #{c: Color, v:Int | post.tiles[c][v] = p}
              drawNewTile[pre, post, p, c, v]
              }
          } 
      } is unsat 
  }
}
---------------------------------------playableSet---------------------------------------

test suite for playableSet {
  //unsat - color and value can't both be equal 
  test expect {
        ps_case1: {
            some c1, c2, c3: Color, v1, v2, v3: Int | 
            {
                c1 = c2 
                c2 = c3
                v1 = v2 
                v2 = v3
                playableSet[c1, c2, c3, v1, v2, v3]
            }
        } is unsat 
  }

  //unsat - consecutive number but colors not equal
  test expect {
        ps_case2: {
            some c1, c2, c3: Color, v1, v2, v3: Int | 
            {
                c1 != c2 
                c2 = c3
                consecutiveNumbers[v1, v2, v3]
                playableSet[c1, c2, c3, v1, v2, v3]
            }
        } is unsat 
  }

  //unsat - numbers same but one of the colors is the same
  test expect {
        ps_case3: {
            some c1, c2, c3: Color, v1, v2, v3: Int | 
            {
                c1 != c2 
                c1 != c3
                c2 = c3
                v1 = v2
                v2 = v3
                playableSet[c1, c2, c3, v1, v2, v3]
            }
        } is unsat 
  }

  //sat - color not equal and value is  
  test expect {
        ps_case4: {
            some c1, c2, c3: Color, v1, v2, v3: Int | 
            {
                c1 != c2 
                c2 != c3
                c3 != c1
                v1 = v2 
                v2 = v3
                playableSet[c1, c2, c3, v1, v2, v3]
            }
        } is sat 
  }

   //sat - color equal and values increasing  
  test expect {
        ps_case5: {
            some c1, c2, c3: Color, v1, v2, v3: Int | 
            {
                c1 = c2 
                c2 = c3
                c3 = c1
                v2 = add[v1, 1]
                v3 = add[v2, 1]
                playableSet[c1, c2, c3, v1, v2, v3]

            }
        } is sat 
  }

   //sat - color equal and values decreasing  
  test expect {
        ps_case6: {
            some c1, c2, c3: Color, v1, v2, v3: Int | 
            {
              c1 = c2 
              c2 = c3
              c3 = c1
              v2 = subtract[v1, 1]
              v3 = subtract[v2, 1]
              playableSet[c1, c2, c3, v1, v2, v3]
            }
        } is sat 
  }

   //sat - colors equal & consecutiveNumbers numbers
  test expect {
        ps_case7: {
            some c1, c2, c3: Color, v1, v2, v3: Int | 
            {
              c1 = c2 
              c2 = c3
              c3 = c1
              consecutiveNumbers[v1, v2, v3]
              playableSet[c1, c2, c3, v1, v2, v3]
            }
        } is sat 
  }
}

---------------------------------------consecutiveNumbers---------------------------------------

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

---------------------------------------canPlayFirstHand---------------------------------------

test suite for canPlayFirstHand {
    /*
    Same funciton as playableSet but with added minimumValue requirement - many of playableSet tests cover this functionality 
    so we just need to test that the additional minVal requirement 
    */


    //Simple test case - if its a playable set that has values > or = to the min val then it satisfies canPlayFirstHand
    test expect {
        cpfh_case1: {
            some p:Pool, player: Player, c1, c2, c3: Color, v1, v2, v3: Int | 
            {
              playableSet[c1, c2, c3, v1, v2, v3]
              add[add[v1, v2], v3] >= 15
              canPlayFirstHand[p, player, 15]
            }
        } is sat 
    }

    //Playable set but dosent meet min val
    test expect {
        cpfh_case2: {
            some p:Pool, player: Player, c1, c2, c3: Color, v1, v2, v3: Int | 
            {
              wellformed
              playableSet[c1, c2, c3, v1, v2, v3]
              add[add[v1, v2], v3] <= 10
              canPlayFirstHand[p, player, 10]
            }
        } is unsat 
    }

    //If not playable set then can not play first hand 
    test expect {
        cpfh_case3: {
            some p:Pool, player: Player, c1, c2, c3: Color, v1, v2, v3: Int | 
            {
              wellformed
              not playableSet[c1, c2, c3, v1, v2, v3]
              canPlayFirstHand[p, player, 10]
            }
        } is unsat 
    }

    //If not playable set then can not play first hand even if v1-v3 meet the min value 
    test expect {
        cpfh_case4: {
            some p:Pool, player: Player, c1, c2, c3: Color, v1, v2, v3: Int | 
            {
              wellformed
              not playableSet[c1, c2, c3, v1, v2, v3]
              add[add[v1, v2], v3] >= 15
              canPlayFirstHand[p, player, 10]
            }
        } is unsat 
    }
}

