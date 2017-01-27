package ss.project.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ss.project.Field;
import ss.project.Mark;
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
    
    @Test
    public void testisEmptyField() {
        Field filler = new Field (1,1,0);
        assertTrue(board.isEmptyField(filler));
        board.setField(filler, Mark.Black);
        assertFalse(board.isEmptyField(filler));
    }
}
