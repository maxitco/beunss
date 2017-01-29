 package ss.project;

import java.io.IOException;
import java.net.Socket;

public class ServerHandler extends Terminal {
    private Client client;
    
    ServerHandler(Client inputClient, Socket inSock) throws IOException {
        super(inSock.getInputStream(), inSock.getOutputStream());
        this.client = inputClient;
    }
    
    @Override
    public void atStart() {
        //nada, wait for capabilities from server first
    }
    
    @Override
    public void handleInput(String input) {
      //split input around spaces
        String[] inputSplit = input.split(" ");
        
        if (inputSplit[0].equals(Protocol.Server.SERVERCAPABILITIES)) {
            send(this.client.getCapabilities());
        } else if (inputSplit[0].equals(Protocol.Server.ASSIGNID)) {
            if (client.isOnline()) {
                this.client.send("Connection established, waiting for other players"); 
            } else if (!client.isOnline()){
                this.client.send("Enter AI difficulty 'easy'/'medium'/'hard'");
            }
        } else if (inputSplit[0].equals(Protocol.Server.STARTGAME)) {
            this.client.send("Game has started");
            //TODO create board for client
        }
        
        else {        
            send("code 4");
        }
    }
}
