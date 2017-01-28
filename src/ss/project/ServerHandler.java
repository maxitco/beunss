package ss.project;

import java.io.IOException;
import java.net.Socket;

public class ServerHandler extends Terminal {
    private Client client;
    
    ServerHandler(Client inputClient, Socket inSock) throws IOException {
        super(inSock.getInputStream(), inSock.getOutputStream());
        this.client = inputClient;
    }
    
    
}
