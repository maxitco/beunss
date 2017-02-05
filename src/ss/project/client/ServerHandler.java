package ss.project.client;

import java.io.IOException;
import java.net.Socket;

import ss.project.game.Mark;
import ss.project.game.Protocol;
import ss.project.view.Terminal;

public class ServerHandler extends Terminal implements Runnable {
    private Client client;    
    
    ServerHandler(Client inputClient, Socket inSock) throws IOException {
        super(inSock.getInputStream(), inSock.getOutputStream());
        this.client = inputClient;
    }
    
    @Override
    public void onFailure() {
      //exit the terminal and close its streams.
        this.client.setInGame(false);
        
        super.exit();
                
        this.client.sendToView("Connection to the server dropped.");
        this.client.sendToView("Enter restart to reconnect to a server.");
    }
    
    @Override
    public void atStart() {
        //nada, wait for capabilities from server first
    }
    
    @Override
    public void send(String input) {
        super.send(input);
        System.out.println(input);
    }
    
    /**
     * handleInput() description.
     * split input around spaces, and determine what action needs to be taken 
     * longer actions are placed in separate functions starting with "at"
     * these functions can be found below handleInput()
     */    
    
    @Override
    public void handleInput(String input) {
        //System.out.println("server sends: " + input); //for testing
        //split input around spaces
        String[] inputSplit = input.split(" ");
        
        if (inputSplit[0].equals(Protocol.ProtServer.SERVERCAPABILITIES)) {
            //respond with capabilities of the client
            send(this.client.getCapabilities());
            if (inputSplit.length > 7 && inputSplit[7].equals("1") && this.client.isOnline()) {
                this.client.canChat = true;
            } else {
                this.client.canChat = false;
            }
        } else if (inputSplit[0].equals(Protocol.ProtServer.NOTIFYMESSAGE) && this.client.canChat) {
            this.client.atNotifyMessage(inputSplit);
        } else if (inputSplit[0].equals(Protocol.ProtServer.ASSIGNID)) {
            this.client.atAssignId(inputSplit);                
        } else if (inputSplit[0].equals(Protocol.ProtServer.STARTGAME)) {
            this.client.atStartGame(inputSplit);            
        } else if (inputSplit[0].equals(Protocol.ProtServer.TURNOFPLAYER)) {
            this.client.atTurnOfPlayer(inputSplit);                        
        } else if (inputSplit[0].equals(Protocol.ProtServer.NOTIFYMOVE)) {
            this.client.atNotifyMove(inputSplit);            
        } else if (inputSplit[0].equals(Protocol.ProtServer.NOTIFYEND) 
            && inputSplit.length == 2 || inputSplit.length == 3
        ) {
            this.client.atNotifyEnd(inputSplit);          
        } else if (inputSplit[0].equals("error") && inputSplit.length == 2) {
            this.client.sendToView(Protocol.getError(inputSplit[1]));
        } else if (inputSplit[0].equals("ping")) {
            //nothing
        } else {        
            this.client.sendToView("Server is sending an unknown command");            
        }
    }
    
    public boolean isYou(String inputId) {
        return Integer.parseInt(inputId) == this.client.getPlayerId();
    }
    
    /**
     * Start "at" functions belonging in handleInput 
     */
    
    
}

