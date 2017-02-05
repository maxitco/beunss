package ss.project.test;

import ss.project.client.*;
import ss.project.game.Board;
import ss.project.game.Mark;

public class AITest {
	/**
	 * Little test environment to test strength of AI against itself or other difficulties.
	 * Complete game will be print to output terminal.
	 * @param args
	 */
	public static void main(String[] args) {
		Board test = new Board();
		//change difficulty to test different AI settings
		ComputerPlayer one = new ComputerPlayer(new Hard());
		ComputerPlayer two = new ComputerPlayer(new Hard());
		Mark m = Mark.X;
		while (!test.hasEnded()) {
			test.setField(one.determineMove(test, m), m);
			if (test.isWinner(m)) {
				System.out.println("one has won");
				System.out.println(test);
				System.exit(0);
			}
			test.setField(two.determineMove(test, m.other()), m.other());
			if (test.isWinner(m.other())) {
				System.out.println("two has won");
				System.out.println(test);
				System.exit(0);
			}
			System.out.println(test);
		}
	}

}
