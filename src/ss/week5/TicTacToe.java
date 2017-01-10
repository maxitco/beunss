package ss.week5;

/**
 * Executable class for the game Tic Tac Toe. The game can be played against the
 * computer. Lab assignment Module 2
 * 
 * @author Theo Ruys
 * @version $Revision: 1.4 $
 */
public class TicTacToe {
    
    
    
    public static void main(String[] args) {
        Player player0,player1;
        if (args.length < 2) {
            System.exit(0);
        }
        
        if (args[0].contains("-N")) {
            player0 = new ComputerPlayer(Mark.XX,new NaiveStrategy());
        }
        else {
            player0 = new HumanPlayer(args[0],Mark.XX);
        }
        if (args[1].contains("-N")) {
            player1 = new ComputerPlayer(Mark.OO,new NaiveStrategy());
        }
        else {
            player1 = new HumanPlayer(args[1],Mark.OO);
        }


        Game game0 = new Game(player0, player1);
        game0.start();
    }
}
