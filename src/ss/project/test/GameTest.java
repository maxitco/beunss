package ss.project.test;

import org.junit.Before;
import org.junit.Test;
import org.junit.*;
import ss.project.Game;

public class GameTest {
    
    public class Turnn {
        public int whoseTurn(int input) {
            return input % (2);
        }
    }
    
    @Before
    public void setUp() {
        
    }
    
    @Test
    public void obtainIdTest() {
        Turnn aTurn = new Turnn();
        System.out.println(aTurn.whoseTurn(1));
        System.out.println(aTurn.whoseTurn(2));
        System.out.println(aTurn.whoseTurn(3));
        System.out.println(aTurn.whoseTurn(4));
    }
}
