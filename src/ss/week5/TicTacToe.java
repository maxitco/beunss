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
        if (args.length < 2) {
            System.exit(0);
        }
        HumanPlayer player0 = new HumanPlayer(args[0],Mark.XX);
        HumanPlayer player1 = new HumanPlayer(args[1],Mark.OO);


        Game game0 = new Game(player0, player1);
        game0.start();
    }
}
