package ss.project;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;



public class ClientTest {
    private static final String USAGE
        = "usage: java week7.cmdline.Client <name> <address> <port>";

    private final Socket sock;
    private BufferedReader in;
    private BufferedWriter out;
    private String playerName;
    private int playerId;
    private Game game;
    private String capabilities;
    
    
    public ClientTest(Socket inSock) throws IOException {
        this.sock = inSock;         
        this.in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
        this.out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
    } 
    

    
    public void setPlayerName(String input) {
        this.playerName = input;
    }
    
    //getPort function to retrieve port from input
    //duplicate Client/Server function getPort()
    //some people might only run the server or only a client
    //so duplicate is required
    public static int getPort(String input) {
        int result = 0;
        try {
            result = Integer.parseInt(input);
        } catch (NumberFormatException e) {
            System.out.println(USAGE);
            System.out.println("ERROR: " + input
                               + " is not an integer");
            System.exit(0);
        }
        return result;
    }
    
    /** Starts a Client application. */
    public static void main(String[] args) {
        if (args.length != 3) {
            System.out.println(USAGE);
            System.exit(0);
        }
    
        
        InetAddress addr = null;
        int port = 0;
        Socket sock = null;
    
        // check args[1] - the IP-adress
        try {
            addr = InetAddress.getByName(args[1]);
        } catch (UnknownHostException e) {
            System.out.println(USAGE);
            System.out.println("ERROR: host " + args[1] + " unknown");
            System.exit(0);
        }
    
        // parse args[2] - the port
        port = getPort(args[2]);
    
        // try to open a Socket 
        try {
            sock = new Socket(addr, port);
        } catch (IOException e) {
            System.out.println("ERROR: could not create a socket on " + addr
                    + " and port " + port);
        }      
        
        //initialize, should be overwritten
        ClientTest aClient = null;
        try {
            aClient = new ClientTest(sock);
            aClient.playerName = args[0];
        } catch (IOException e1) {
            System.out.println("Could not construct, error with making buffered reader/writer");
        }
        
        String line = null; 
        try { 
                               
            while (true) { 
                while ((line = aClient.in.readLine()) != null) {
                    System.out.println(line);
                }
            } 
        } catch (IOException e) { 
            System.out.println("Something went wrong reading from socket"); 
        } 
    
    }   
}
