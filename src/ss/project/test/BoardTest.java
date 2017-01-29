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
        Field badfield = new Field(board.MAXFIELD + 1,0,0);
        Field goodfield = new Field(1,1,0);
        assertTrue(board.isField(goodfield));
        assertFalse(board.isField(badfield));
    }
    
    @Test
    public void testisEmptyField() {
        Field filler = new Field (1,1,0);
        assertTrue(board.isReachableEmptyField(filler));
        board.setField(filler, Mark.Black);
        assertFalse(board.isReachableEmptyField(filler));
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
    
    @Test
    public void testsetField() {
        //wrong move
        Field test0 = new Field(1, 1, 1);
        assertFalse(board.setField(test0, Mark.White));
        assertTrue(board.getMark(test0) == null);
        //correct move
        Field test1 = new Field(1, 1, 0);
        assertTrue(board.setField(test1, Mark.Black));
        assertEquals(board.getMark(test1), Mark.Black);
        //out of bounds stacking with coordinates
        for (int i = 0; i <= board.MAXFIELD;i++) {
            assertTrue(board.setField(0, 0, Mark.White));
        }
        assertFalse(board.setField(0, 0, Mark.Black));
        //check coordinate setting worked correctly
        Field coord = new Field(0, 0, 0);
        assertEquals(board.getMark(coord),Mark.White);
    }
    
    @Test
    public void testwalkField() {
        Field start = new Field(0, 0, 0);
        Field end = new Field(1, 1, 1);
        start = board.walkField(start, 1, 1, 1);
        assertEquals(end, start);
    }
    
    @Test
    public void testgetMark() {
        Field test = new Field(0, 0, 0);
        assertEquals(null, board.getMark(test));
        board.setField(test, Mark.Black);
        assertEquals(Mark.Black, board.getMark(test));
    }
    
    @Test
    public void testreset() {
        Field test = new Field(0, 0, 0);
        board.setField(test, Mark.Black);
        assertEquals(Mark.Black, board.getMark(test));
        board.reset();
        assertEquals(null, board.getMark(test));
    }
    
    @Test
    public void testcheckRow() {
        Mark m0 = Mark.Black;
        Mark m1 = Mark.White;
        Field start = new Field(0, 0, 0);
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            board.setField(i, 0, m0);
        }
        for (int i = 1; i <= Board.MAXFIELD; i++) {
            board.setField(i, i, m1);
        }
        assertTrue(board.checkRow(start, 1, 0, 0, m0));
        assertFalse(board.checkRow(start, 1, 1, 0, m1));
    }
    
    @Test
    public void testcheckZColums() {
        //horizontal row
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            board.setField(i, 0, Mark.Black);
        }
        assertFalse(board.checkZcolums(Mark.Black));
        //stack column
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            board.setField(1, 1, Mark.Black);
        }
        assertTrue(board.checkZcolums(Mark.Black));
    }
}
