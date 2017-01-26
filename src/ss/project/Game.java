package ss.project;

import java.util.ArrayList;

public class Game extends Thread {
    private ArrayList<ClientHandler> playerList = new ArrayList<ClientHandler>();
    private Board board;
    private boolean running = false;
    private boolean answered; //used for keeping track of client response
    
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
        if (this.running == false) {
            this.start();
            this.running = true;
        }
    }
    
    public synchronized void makeMove() {
        
    }
    
    public void run() {
        //counts at which turn the game is, start with turn 1
        int turnCounter = 1;
        
        while (true) {
            //determine whose turn it is, depending on turn and amount of players
            int i = turnCounter % (playerList.size()-1);
            
            for (ClientHandler c: this.playerList) {
                c.send(Protocol.Server.TURNOFPLAYER + " " + playerList.get(i).getPlayerId());
            }
            //set answered on false, is set true when the player whose turn it is makes a move
            this.answered = false;
            
            //wait for move
            while (!answered) {
                
            }
            turnCounter++; //next turn
        }
    }
}
