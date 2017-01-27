package ss.project.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ss.project.Field;
import ss.project.Board;

public class BoardTest {
    private Board board;
    @Before
    public void setUp() throws Exception {
       this.board = new Board();
    }

    @Test
    public void testisField() {
        Field badfield = new Field(4,0,0);
        Field goodfield = new Field(2,3,0);
        assertTrue(board.isField(goodfield));
        assertFalse(board.isField(badfield));
    }
    

}
