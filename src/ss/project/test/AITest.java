package ss.project.test;

import ss.project.*;

public class AITest {

	public static void main(String[] args) {
		Board test = new Board();
		ComputerPlayer one = new ComputerPlayer(new Medium());
		ComputerPlayer two = new ComputerPlayer(new Medium());
		Mark m = Mark.Black;
		while(!test.hasEnded()) {
			test.setField(one.determineMove(test, m), m);
			test.setField(two.determineMove(test, m.other()), m.other());
			System.out.println(test);
		}
	}

}
