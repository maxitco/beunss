package ss.project.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;
import ss.project.server.*;
import java.io.IOException;



public class ServerTest {
    private ServerTestThread serverThread;    
    
    public Server getServer() {
        return this.serverThread.server;
    }
    
    @Before
    public void setUp() {
        this.serverThread = new ServerTestThread();
        this.serverThread.start();
        //5 sec to enter port 10
        try {
            Thread.sleep(5000);
        } catch(InterruptedException e) {
            
        }
    }
    
    @Test
    //requires visual inspection of console
    public void sendToViewTest() {        
        if(getServer() != null) {
            getServer().sendToView("hi");
        } else {
            System.out.println("wtf?");
        }
    }
    
    @Test
    public void InitialTest() {
        assertTrue(getServer().getGameList().size() == 0);
        assertTrue(getServer().getClientHandlerList().size() == 0);
    }
    
    

}
