# Logic 4 Systems: Curiosity Modeling by @lmckeown and @wbednarz #
<ln/>

## Project Objective: 
### What are you trying to model? 

For this project, we choose to model a simplified version of the game of <b> Rummikub </b>. Rumikub is a tile-based game 
for 2 to 4 players and combines elements of the card game rummy and mahjong. For our modeling purposes, we wanted to focus on a 
specific rule of the game: you have to have a hand with a specific number of points to play your first turn. To model 
these 'first hand' cases in Froglet, we have made small changes to the original rules of Rummikub that will be explained in detail below. Enjoy!

### Helpful Context: Rummikub vs. Froglet Rummikub Rules and Gameplay

##### Game Setup
###### Origional Rummikub
- There are 106 tiles [1-13 red, blue, green and yellow (x2) + two jokers] [2-4 players]
- Game tiles are placed face down in on the table, each player picks up an original hand of 14 tiles and places their tiles on their rack.

###### Froglet Rummikub
- There are 52 tiles [1-3 red, blue, green and yellow] [2 players]
- Game tiles are represented by a rxc matrix where rows represent color and cols represent value. Each matrix index will be empty when the game begins.
  Players will 'pick up tiles' by placing their player name at a rxc matrix index. (ex: tiles[Red][2] = A -> player A has the Red 2 tile in their hand)
- Each player will start with 7 tiles

##### First Turn 
###### Origional Rumikub
The first player's initial move must meet certain requirements:
-- The player must place tiles on the table that have a total value of at least 30 points.
-- The tiles placed on the table must form valid set.
-- The initial meld can consist of one or more sets or runs.

###### Froglet Rummikub
The first player's initial move must meet a certain requirement:
-- The player must place tiles on the table that have a total value of at least 15 points.
-- The tiles placed on the table must form either a single valid set. 

##### What is a valid set?
A valid set is a group or run of tiles
--<b>RUN</b>: a set of three or more consectutive numbers all in the same color.
--<b>GROUP</b>: 3 or 4 tiles that have are the same value and are different colors.

To view the full rules of the game please visit [this](https://rummikub.com/wp-content/uploads/2019/12/2600-English-1.pdf) site. 

### Our BIG Question
A big part of the game Rummikub is the aspect of manipulation, when both players have been able to play their first hand, they can add to or restructure 
the tiles on the board when attempting to play all the tiles in their hand. Modeling this idea of manipulation is complex; however, modeling first turn scenarios
which start this process is an important step to understanding modeling the full game. The purpose of this project is to get a better understanding of these first-turn 
scenarios, which can happen at any point in the game after the original hand tiles are chosen!  

<ln/>

### Model Design and Visualization: 
#### Model Design Choices

###### Rummikub
In the Rummikub game, game tiles are placed face down on the table in a 'tile pool'. Players then randomly choose tiles and place the tile on their 'tray' to represent their hand. This setup is visually shown in the image below
![Rummikub Setup](rumikub_setup.jpeg)

###### Froglet Rummikub
To model this setup in Froglet Rummikub, we use an n (color) x m (value) matrix to represent all the tiles in a game. Within the matrix, if a specific color+value tile has nothing at its rxc position '''pool.tiles[color][value] = null''', the tile is in the 'tile pool'. If the rxc position has a player in the position ~~~pool.tiles[color][value] = B~~~ or ~~~pool.tiles[color][value] = A~~~, the tile is in the perspective player's 'tray' or hand. A visual representation with a sterling visualizer example in Forge/Froglet is provided below.
![Forgeex](forge_ex.jpeg)

#### Run Statements 

#### How should we look at and interpret an instance created by your spec | Sterling visualizer | Did you create a custom visualization, or did you use the default?

### Signatures and Predicates: 
At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

### Testing:  
What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.

### Documentation:  
Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.
