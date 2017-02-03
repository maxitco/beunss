package ss.project.test;

import ss.project.*;
import ss.project.client.ComputerPlayer;
import ss.project.client.Hard;
import ss.project.game.Board;
import ss.project.game.Mark;

public class AITest {

	public static void main(String[] args) {
		Board test = new Board();
		ComputerPlayer one = new ComputerPlayer(new Hard());
		ComputerPlayer two = new ComputerPlayer(new Hard());
		Mark m = Mark.Black;
		while(!test.hasEnded()) {
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
