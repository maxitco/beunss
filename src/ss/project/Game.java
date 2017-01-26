package ss.project;

import java.util.ArrayList;

public class Game extends Thread {
    private ArrayList<ClientHandler> playerList = new ArrayList<ClientHandler>();
    private Board board;
    private boolean running = false;
    
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
    
    public void run() {
        
    }
}
