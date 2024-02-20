#lang forge/bsl
/*
DEVIATIONS FROM STANDARD GAME OF RUMMIKUB:
1: One player only
2: No repeated tiles [one set of each tile color pair only]
3: No jokers
4: Tiles only go up to 7
5: First move has to add up to 15
*/

abstract sig Player {} 
one sig A extends Player {} //one player for now 

sig Pool {
    -- each row represents a tile color [Red, Blue, Green, Yellow]
    -- each col represents a tile value [1 - 7]
    -- None - tile is in the pool, Player - tile is in Player, p's hand
    tiles: pfunc Color -> Int -> Player
}

abstract sig Color {}
one sig Red extends Color {}
one sig Blue extends Color {}
one sig Green extends Color {}
one sig Yellow extends Color {}

pred validTiles[p : Pool] {
  //make sure only one player is on each tile or its empty -- singleton queens 
  all c : Color | { 
    all v : Int | {
      //color is valid (look back at this if there are problems)
      (v >= 1 and v <= 7) => {
        no p.tiles[c][v] or p.tiles[c][v] = A
      }
    }
  }
  // (#{c: Color, v:Int | p.tiles[c][v] = A} = 3)
}

pred wellformed {
  all p: Pool | { 
    all color: Color, value: Int | {
      (value < 1 or value > 7) => {
          no p.tiles[color][value]
      }
    } 
  }
}

//may make this so player A has 7 tiles initiallly, or write seperate function
pred init[p: Pool] {
  // initialize the tile pool to all the tiles
  //each player has 14 tiles in their hand 
  // have A draw 14 times
  //no one is anywhere on board 
  //board is 

  all color: Color, value: Int | no p.tiles[color][value]
} 

//TODO: make color color sig that just abstracts int
pred drawNewTile[pre, post : Pool, p: Player, color: Color, value: Int] {
  // find some way to restrict value to 1-8
  // similar to move in tic tac toe
  // compare player before hand to after hand
  no pre.tiles[color][value]
  post.tiles[color][value] = p
  // //make sure all the others are unchanged
  all c2 : Color, v2 : Int | (c2!=color or v2!=value) => {
    post.tiles[c2][v2] = pre.tiles[c2][v2]
  }
}

//Can we play this set of tiles as a valid move?
//Criteria: 
// 1: Must be a run of 3 or more TileValue of all the same TileColor
// OR
// 2: 3 or 4 tiles, same TileValue but different TileColor
// Note: Runs are non-cyclic, aka 1(the lowest number) cannot follow 7(the biggest number)!

pred playableSet[color1, color2, color3 : Color, value1, value2, value3 : Int] {
  (
    color1 = color2 and color2 = color3 and 
    consecutiveNumbers[value1, value2, value3])
  or
  (
  value1 = value2 and value2 = value3 and
  color1 != color2 and color2 != color3 and color1 != color3
  )

}

pred consecutiveNumbers[v1, v2, v3 : Int] {
  v1 != v2
  v2 != v3
  v1 != v3
  //v1 < v2 < v3
  v1 < v2 and v2 < v3 => {
    (subtract[v2, v1] = 1) and (subtract[v3, v2] = 1)
  }
  //v1 < v3 < v2
  v1 < v3 and v3 < v2 => {
    (subtract[v3, v1] = 1) and (subtract[v2, v3] = 1)
  }
  //v2 < v1 < v3
  v2 < v1 and v1 < v3 => {
    (subtract[v1, v2] = 1) and (subtract[v3, v1] = 1)
  }
  //v2 < v3 < v1
  v2 < v3 and v3 < v1 => {
    (subtract[v3, v2] = 1) and (subtract[v1, v3] = 1)
  }
  //v3 < v1 < v2
  v3 < v1 and v1 < v2 => {
    (subtract[v1, v3] = 1) and (subtract[v2, v1] = 1)
  }
  //v3 < v2 < v1
  v3 < v2 and v2 < v1 => {
    (subtract[v2, v3] = 1) and (subtract[v1, v2] = 1)
  }
}

pred canPlayFirstHand[p: Pool] {
  // some set in the players hand such that
  // playableset[set]
  // AND
  // sum[set] >= 15
  some color1, color2, color3 : Color, value1, value2, value3 : Int | {
    playableSet[color1, color2, color3, value1, value2, value3]
    p.tiles[color1][value1] = A
    p.tiles[color2][value2] = A
    p.tiles[color3][value3] = A
    //adds up to 7
    add[add[value1, value2], value3] >= 5
  }
}

// //For find valid draw
// run {
//   some pre, post : Pool, color : Color, value : Int | {
//     // init[pre]
//     wellformed
//     validTiles[pre]
//     validTiles[post]
//     drawNewTile[pre, post, A, color, value]

  
//   }
// } for 2 Pool, 4 Color, 4 Int, 1 Player

//For finding valid hand to play
run {
  some p : Pool | {
    wellformed
    validTiles[p]
    canPlayFirstHand[p]
  }
} for 1 Pool, 4 Color, 4 Int, 1 Player