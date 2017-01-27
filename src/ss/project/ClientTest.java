package ss.project;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;



public class ClientTest {
    private static final String USAGE
    = "usage: java week7.cmdline.Client <name> <address> <port>";

    
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
    
        String name = args[0];
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
    }   
}
