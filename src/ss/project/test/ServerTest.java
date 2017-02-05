package ss.project.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;
import ss.project.server.*;
import ss.project.client.*;
import java.io.IOException;



public class ServerTest {
    private ServerTestThread serverThread;    
    private Server serv;
    
    public Server getServer() {
        if (this.serverThread != null) {
            return this.serverThread.server;
        } else {
            return this.serv;
        }
    }
    
    @Before
    public void setUp() {
        this.serv = new Server();
        
        //sleep 0.1 sec to make sure server started
        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
            
        }
    }
    
    @Test
    //requires visual inspection of console
    public void sendToViewTest() {        
        if (getServer() != null) {
            getServer().sendToView("hi");
        } else {
            System.out.println("no server?");
        }
    }
    
    @Test
    public void InitialTest() {
        assertEquals(0, getServer().getGameList().size());
        assertEquals(0, getServer().getClientHandlerList().size());
        
        assertEquals(10, getServer().getPort("10"));
        assertEquals(0, getServer().getPort("yoyo"));
    }
    
    
    //start server on port 10
    //connect many clients
    //check nr of clients, nr of games
    
    
    @Test
    public void connectingHandlersTest() {
        this.serverThread = new ServerTestThread();
        this.serverThread.start();
       
        //give some starting time to new thread
        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
        //nada     
        }
        
        //start the server on port 10
        this.serverThread.server.startServer("10");
        
        //wait for it to start
        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
        //nada     
        }
        
        for (int i = 0; i < 1001; i++) {
            Client client = new Client();
            client.setOnline(true);
            int nr = i + 1;
            client.setPlayerName("simulator:" + nr);
            client.connectToServer("localhost", "10");
        }
        
        //give server some time to deal with connects
        try {
            Thread.sleep(5000);
        } catch (InterruptedException e) {
        //nada     
        }
        
        assertEquals(1001, getServer().getClientHandlerList().size());
        assertEquals(501, getServer().getGameList().size());    
        assertTrue(getServer().getGameList().get(0).isFull());
        assertTrue(getServer().getGameList().get(1).isFull());
        assertTrue(getServer().getGameList().get(2).isFull());
        //game with last client should not be full
        assertTrue(!getServer().getGameList().get(500).isFull());
    }
    
    
    //start new server on port 20
    //connect some ai clients
    //let them play against eachother
    @Test
    public void aiPlayGamesTest() {
        this.serverThread = new ServerTestThread();
        this.serverThread.start();
        
       
        //give some starting time to new thread
        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
        //nada     
        }
        
        //start the server on port 20
        this.serverThread.server.startServer("20");
        
        //wait for it to start
        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
        //nada     
        }
        
        for (int i = 0; i < 5; i++) {
            Client client = new Client();
            client.setOnline(true);
            int nr = i + 1;
            client.setPlayerName("simulator:" + nr);
            //turn on the ai
            client.toggleAI();
            client.connectToServer("localhost", "20");
        }
        
        //give server a minute time to let games run
        try {
            Thread.sleep(10000);
        } catch (InterruptedException e) {
        //nada     
        }
        
        //clients are kicked if their game ends
        assertEquals(1, getServer().getClientHandlerList().size());
        //other games should finish, so only game remains
        assertEquals(1, getServer().getGameList().size()); 
    }
}
