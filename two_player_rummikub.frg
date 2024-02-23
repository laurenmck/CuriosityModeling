#lang forge/bsl
/*

For this project, Will and I choose to model a simplified version of the game of Rummikub. Rumikub is a tile-based game 
for 2 to 4 players and combines elements of the card game rummy and mahjong. For our modeling purposes, we wanted to focus on a 
specific rule of the game, that is you have to have a hand with a specific number of points to play your first turn. To model 
these 'first hand' cases in forge, we have made small changes to the origional rules of Rummikub that will be explained in detail below. Enjoy!

-----GAME SET UP-----

**Origional Rummikub**
- There are 106 tiles [1-13 red, blue, green and yellow (x2) + two jokers] [2-4 players]
- Game tiles are placed face down in on the table, each player picks up an origional hand of 14 tiles and places their tiles on their rack.

**Forge Rummikub**
- There are 52 tiles [1-3 red, blue, green and yellow] [2 players]
- Game tiles are represented by a rxc matrix where rows represent color and cols represent value. Each matrix index will be empty when the game begins.
  Players will 'pick up tiles' by placing their player name at a rxc matrix index. (ex: tiles[Red][2] = A -> player A has the Red 2 tile in their hand)
- Each player will start with 7 tiles 

--First Turn--

**Origional Rummikub**
The first player's initial move must meet a certain requirement:
-- The player must place tiles on the table that have a total value of at least 30 points.
-- The tiles placed on the table must form valid set.
-- The initial meld can consist of one or more sets or runs.

**Forge Rummikub**
The first player's initial move must meet a certain requirement:
-- The player must place tiles on the table that have a total value of at least 15 points.
-- The tiles placed on the table must form either a single valid set. 

--Valid Set--

A valid set is a group or run of tiles
--RUN: a set of three or more consectutive numbers all in the same color.
--GROUP: 3 or 4 tiles that have are the same value and are different colors.
*/

-- game players 
abstract sig Player {} 
one sig A, B extends Player {}

-- pool to represent the game tiles 
sig Pool {
    -- each row represents a tile color [Red, Blue, Green, Yellow]
    -- each col represents a tile value [1 - 7]
    -- tiles[r][c] = None => tile is in the pool 
    -- tiles[r][c] = A/B => tile is in player A/B's hand
    tiles: pfunc Color -> Int -> Player
}

-- color to represent the possible tile colors
abstract sig Color {}
one sig Red extends Color {}
one sig Blue extends Color {}
one sig Green extends Color {}
one sig Yellow extends Color {}

/*
The wellformed predicate rules out garbage tile values: 
for all tile pools and color/value pairs, the values cannot be less than 1 or greater than 13. We have defined the 
4 possible color values on the board, so color being [red, blue, green or yellow is implies]
*/
pred wellformed {
  all p: Pool | { 
    all color: Color, value: Int | {
      (value < 1 or value > 13) => {
          no p.tiles[color][value]
      }
    } 
  }
}

/*
The validTiles predicate takes in a pool of tiles and indicated is the tiles represented in a valid manner. 

A valid tile is either: 
1. Empty or in the general pool (tiles.[color][value] = None)
2. In player A's hand (tiles.[color][value] = A)
3. In player B's hand (tiles.[color][value] = B)

Two players cannot have the same tile.
*/
pred validTiles[p : Pool] {
  all c : Color | { 
    all v : Int | {
      (v >= 1 and v <= 13) => {
        no p.tiles[c][v] or p.tiles[c][v] = A or p.tiles[c][v] = B
      }
    }
  }
}

/*
The init predicate initializes all the game tiles, no player has any tiles at the start of the game.
*/
pred init[p: Pool] {
  all color: Color, value: Int | no p.tiles[color][value]
} 

/*
The drawNewTile predicate takes in a pre, post pool, a player and a color, int pair and models the action 
of a player drawing a new tile into their hand. 
*/
pred drawNewTile[pre, post : Pool, p: Player, color: Color, value: Int] {

  --tile place must be un-claimed before the player can claim that tile
  no pre.tiles[color][value]
  post.tiles[color][value] = p

  --all other tiles in the pool remain unchanged after this play
  all c2 : Color, v2 : Int | (c2!=color or v2!=value) => {
    post.tiles[c2][v2] = pre.tiles[c2][v2]
  }
}

/*
The playableSet predicate determines if a player can play the input set of tiles as a valid move. To be a valid move 

//Criteria: 
// 1: Must be a run of 3 or more TileValue of all the same TileColor
// OR
// 2: 3 or 4 tiles, same TileValue but different TileColor
// Note: Runs are non-cyclic, aka 1(the lowest number) cannot follow 7(the biggest number)!
*/
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

/*
The consecutiveNumbers predicate is a helper predicate for playableSet that returns true if
the inputs v1, v2 and v3 are consecutive numbers.
*/
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

/*
The canPlayFirstHand predicate takes in a pool, player and minimumValue and checks if there are some set of three tiles 
in the players hand that satifsy the playableSet predicate and add up to the minimumValue requirement for the first turn.
*/
pred canPlayFirstHand[p: Pool, player : Player, minimumValue : Int] {
  // some set in the players hand such that
  // playableset[set]
  // AND
  // sum[set] >= 15
  some color1, color2, color3 : Color, value1, value2, value3 : Int | {
    playableSet[color1, color2, color3, value1, value2, value3]
    p.tiles[color1][value1] = player
    p.tiles[color2][value2] = player
    p.tiles[color3][value3] = player
    //adds up to 7
    add[add[value1, value2], value3] >= minimumValue
  }
}

//Run statement to find minimum value such that both players cant play
run {
  some minVal : Int | {
    some p : Pool | {
      wellformed
      validTiles[p]
      (canPlayFirstHand[p, A, minVal] and not canPlayFirstHand[p, B, minVal]) or (not canPlayFirstHand[p, A, minVal] and canPlayFirstHand[p, B, minVal]) or (canPlayFirstHand[p, A, minVal] and canPlayFirstHand[p, B, minVal])
      (#{c: Color, v:Int | p.tiles[c][v] = A} = #{c: Color, v:Int | p.tiles[c][v] = B})
      (#{c: Color, v:Int | p.tiles[c][v] = A} >= 7) // must start with at least 7 cards 
      //add so that they both have same number tiles
    }
  }
} for 2 Player, 1 Pool, 4 Color, 5 Int

//Run statement to see if we have no shot with 6 cards
// run {
//   some p : Pool | {
//     wellformed
//     validTiles[p]
//     not canPlayFirstHand[p]
//     (#{c: Color, v:Int | p.tiles[c][v] = A} = 6)
//   }
// } for 1 Pool, 4 Color, 4 Int, 1 Player