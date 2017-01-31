package ss.project;

import java.util.ArrayList;

public class Game extends Thread {
    private ArrayList<ClientHandler> playerList = new ArrayList<ClientHandler>();
    private Board board;
    private boolean running = false; //used to disable double start by thread
    private boolean answered; //used for keeping track of client response
    /*
     * counts at which turn the game is
     * starts at 0 since turnCounter++ is at the top of the while loop
     */
    private int turnCounter = 0; 
    private boolean ended = false; //used to shutdown the game
    private int timoutCounter;
    
    public Game() {
        this.board = new Board();
    }
    
    public boolean isFull() {
        if (playerList.size() == 2) {
            return true;
        } else {
            return false;
        }
    }
    
    public synchronized void addPlayer(ClientHandler inputPlayer) {
        playerList.add(inputPlayer);
    }
    
    public ArrayList<ClientHandler> getPlayerList() {
        return this.playerList;
    }  
    
    //make move depending on input, player input is to identify who is trying to make a move
    public synchronized void makeMove(int x, int y, ClientHandler player) {
        //check if it is the turn of the player that calls the function
        
        if (!answered && playerList.get(whoseTurn()).equals(player)) {
            
            //make the move, mark depends on index in the array
            //0 --> black
            if (whoseTurn() == 0) {
                //try to make the move, if valid set answered true 
                if (board.setField(x, y, Mark.Black)) {
                    notifyMove(x, y, player.getPlayerId());                    
                } else {
                    player.send("error 5"); //invalid --> return error 5 (invalid move)
                }
            //1 --> white
            } else {
              //try to make the move, if valid set answered true 
                if (board.setField(x, y, Mark.White)) {
                    notifyMove(x, y, player.getPlayerId());                    
                } else {
                    player.send("error 5"); //invalid --> return error 5 (invalid move)
                }                
            }

        } else {
            player.send("error 5"); //not his turn --> return error 5 (invalid move)
        }
        
    }
    
    //notify all players which move was made
    public void notifyMove(int x, int y, int id) {
        for (ClientHandler c: this.playerList) {
            c.send(Protocol.Server.NOTIFYMOVE + " " + id + " " + x + " " + y);
        }
        //set answered on true such that the game thread can continue
        this.answered = true;
    }
    
    //determine whose turn it is, depending on turn and amount of players
    public int whoseTurn() {
        return this.turnCounter % (2);
    }
    
    //check if the game has ended
    public void gameEnd() {
        //check for winner first, someone could win at turn 64
        if (this.board.isWinner(Mark.Black)) {         
            notifyEnd(this.playerList.get(0).getPlayerId());   
            this.ended = true;
        } else if (this.board.isWinner(Mark.White)) {
            notifyEnd(this.playerList.get(1).getPlayerId());
            this.ended = true;
        //then check for draw
        } else if (this.turnCounter == 64) {
            notifyEnd();
            this.ended = true;
        }  
        //do nothing if not ended
    }
    
    //notify everyone that the game has ended, for win
    public void notifyEnd(int playerId) {
        for (ClientHandler c: this.playerList) {
            c.send(Protocol.Server.NOTIFYEND + " 1 " + playerId);
        }  
    }
    
    //notify everyone that the game has ended, draw
    public void notifyEnd() {
        for (ClientHandler c: this.playerList) {
            c.send(Protocol.Server.NOTIFYEND + " 2");
        }  
    }
    
    @Override
    public void run() {
        //assign an id to each player (their index in the arrayList + 1)
        for (int i = 0; i < this.playerList.size(); i++) {
            int id = i + 1;
            this.playerList.get(i).setPlayerId(id);
            this.playerList.get(i).send(Protocol.Server.ASSIGNID + " " + Integer.toString(id));
        }
        
        //notify players that the game has started   
        //includes game specifications and opponent info
        for (ClientHandler c: this.playerList) {
            c.send(
                    Protocol.Server.STARTGAME 
                    + " 4|4|4|4 " 
                    + getPlayerList().get(0).getPlayerId()
                    + "|" + getPlayerList().get(0).getPlayerName()
                    + "0000ff"
                    + " "
                    + getPlayerList().get(1).getPlayerId()
                    + "|" + getPlayerList().get(1).getPlayerName()
                    + "ff0000" 
            );          
        }      
                        
        while (!this.ended) {     
            this.turnCounter++; //next turn, at top of loop such that not updated when game is ended
            for (ClientHandler c: this.playerList) {
                c.send(
                    Protocol.Server.TURNOFPLAYER + " " 
                    + Integer.toString(playerList.get(whoseTurn()).getPlayerId())
                );          
            }
            //set answered on false, is set true when the player whose turn it is makes a move
            this.answered = false;
            //wait for move
            
            while (!this.answered) {
                try {
                     
                    this.sleep(10);                    
                } catch (InterruptedException e) {
                    //nada
                }
            }   
            //check if the game has ended
            gameEnd();            
        }
    }
}
