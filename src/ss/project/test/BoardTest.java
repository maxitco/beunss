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
    
    @Test
    public void testgetEmptyField() {
        Field free0 = board.getEmptyField(1, 1);
        Field expected0 = new Field(1,1,0);
        assertEquals(expected0,free0);
        board.setField(free0, Mark.Black);
        Field free1 = board.getEmptyField(1, 1);
        Field expected1 = new Field(1,1,1);
        assertEquals(expected1,free1);
        
    }
    
    public void testsetField() {
        
    }
    @Test
    public void testwalkField() {
        Field start = new Field(0,0,0);
        Field end = new Field(1,1,1);
        start = board.walkField(start, 1, 1, 1);
        assertEquals(end,start);
    }
}
