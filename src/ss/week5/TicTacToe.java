package ss.week5;

/**
 * Executable class for the game Tic Tac Toe. The game can be played against the
 * computer. Lab assignment Module 2
 * 
 * @author Theo Ruys
 * @version $Revision: 1.4 $
 */
public class TicTacToe {
    
    private Player ArgRead(String arg) {
        switch (arg) {
        case "-N":
            return new ComputerPlayer(Mark.XX,new NaiveStrategy());
            break;
        default:
            return new
    }
    
    public static void main(String[] args) {
        if (args.length < 2) {
            System.exit(0);
        }
        for (int i = 0; i < args.length;i++) {
            switch (args[i]) {
            
            }
        }
        if (args[0].equals("-N")) {
            ComputerPlayer player0 = new ComputerPlayer(Mark.XX,new NaiveStrategy());
        }
        else {
            HumanPlayer player0 = new HumanPlayer(args[0],Mark.XX);
        }
        HumanPlayer player1 = new HumanPlayer(args[1],Mark.OO);


        Game game0 = new Game(player0, player1);
        game0.start();
    }
}
