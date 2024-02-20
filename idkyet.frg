#lang forge/bsl
/*
DEVIATIONS FROM STANDARD GAME OF RUMMIKUB:
1: One player only
2: No repeated tiles
3: No jokers
4: Tiles only go up to 7
5: First move has to add up to 15
*/

abstract sig Player {} 
one sig A, B extends Player {} //one player for now 

one sig Pool {
    -- each row represents a tile color 
    -- each col represents a tile value
    -- player represents who has that tile in their hand 
    -- colors [0: red 1: blue 3: yellow 4: green] 
    -- valyes: 1 - 7   
    tiles: pfunc Color -> Int -> Player
}

abstract sig Color {}
one sig Red extends Color {}
one sig Blue extends Color {}
one sig Green extends Color {}
one sig Yellow extends Color {}

pred validTiles[p : Player] {
  //make sure only one player is on each tile or its empty -- singleton queens 
  all c : Color | { 
    all v : Int | {
      //color is valid (look back at this if there are problems)
      (v >= 1 and v <= 7) => {
        no Pool.tiles[c][v] or Pool.tiles[c][v] = p
      }
    }
  }
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
  value >= 1
  value <= 7
  no pre.tiles[color][value]
  post.tiles[color][value] = p

  //make sure all the others are unchanged
  all c2 : Color, v2 : Int | (c2!=color or v2!=value) => {
    post.tiles[c2][v2] = pre.tiles[c2][v2]
  }
}

//Can we play this set of tiles as a valid move?
//Criteria: 
// 1: Must be a run of 3 or more TileValue of all the same TileColor
// OR
// 2: 3 or 4 tiles, same TileValue but different TileColor
// Note: Runs are non-cyclic, aka 1(the lowest number) cannot follow 13(the biggest number)!

// pred playableSet[ts: Pool] {
// }

pred canPlayFirstHand {
  // some set in the players hand such that
  // playableset[set]
  // AND
  // sum[set] >= 30
}

run {
  some pre, post : Pool, p : Player | {
    // init[pre]
    // wellformed
    // validTiles[p]
    some color : Color, value : Int | {
      drawNewTile[pre, post, p, color, value]
    }
  }
} for 2 Pool, 4 Color, 4 Int, 1 Player