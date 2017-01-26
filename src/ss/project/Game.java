package ss.project;

import java.util.ArrayList;

public class Game {
    private ArrayList<ClientHandler> playerList = new ArrayList<ClientHandler>();
    private Board board;
    
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
}
