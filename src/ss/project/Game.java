package ss.project;

import java.util.ArrayList;

public class Game extends Thread {
    private ArrayList<ClientHandler> playerList = new ArrayList<ClientHandler>();
    private Board board;
    private boolean running = false;
    private boolean answered; //used for keeping track of client response
    private int turnCounter = 1;
    
    public Game() {
        this.board = new Board();
    }
    
    public synchronized boolean isFull() {
        if (playerList.size() == 2) {
            return true;
        } else return false;
    }
    
    public synchronized void addPlayer(ClientHandler inputPlayer) {
        playerList.add(inputPlayer);
    }
    
    public ArrayList<ClientHandler> getPlayerList() {
        return this.playerList;
    }
    
    //starts the game thread, if it is not running already
    public synchronized void startGame() {
        if (!this.running) {
            this.start();
            this.running = true;
        }
    }
    
    //make move depending on input, the id needs to be provided directly by the clienthandler
    public synchronized void makeMove(int x, int y, int id) {
        //check if it is the turn of the player that calls the function
        if (playerList.get(turnOfPlayer()).getPlayerId() == id) {
            
            //make the move, mark depends on index in the array
            if (turnOfPlayer() == 0) {
                //try to make the move, if valid set answered true 
                if (board.setField(x, y, Mark.Black)) {
                    answered = true;
                } else {
                    //invalid --> return error 5 (invalid move)
                    playerList.get(turnOfPlayer()).send("error 5");
                }
            } else {
              //try to make the move, if valid set answered true 
                if (board.setField(x, y, Mark.White)) {
                    answered = true;
                } else {
                    //invalid --> return error 5 (invalid move)
                    playerList.get(turnOfPlayer()).send("error 5");
                }                
            }

        } else {
            
        }
        
    }
    
    //determine whose turn it is, depending on turn and amount of players
    public int turnOfPlayer() {
        return this.turnCounter % (this.playerList.size());
    }
    
    public void run() {
                        
        while (true) {
            
           
            
            for (ClientHandler c: this.playerList) {
                c.send(Protocol.Server.TURNOFPLAYER + " " + playerList.get(turnOfPlayer()).getPlayerId());
            }
            //set answered on false, is set true when the player whose turn it is makes a move
            this.answered = false;
            
            //wait for move
            while (!answered) {
                
            }
            this.turnCounter++; //next turn
        }
    }
}
