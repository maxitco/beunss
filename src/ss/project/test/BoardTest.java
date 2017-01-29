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
        for (int i = 0; i <= board.MAXFIELD; i++) {
            assertTrue(board.setField(0, 0, Mark.White));
        }
        assertFalse(board.setField(0, 0, Mark.Black));
        //check coordinate setting worked correctly
        Field coord = new Field(0, 0, 0);
        assertEquals(board.getMark(coord), Mark.White);
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
        Field badfield = new Field(-1, 0, 0);
        assertEquals(null, board.getMark(badfield));
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
        Field wrongstart = new Field(1, 0, 0);
        assertFalse(board.checkRow(wrongstart, 1, 0, 0, m0));
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
    
    @Test
    public void testcheckPlanes() {
        //horizontal row in xy-plane
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            board.setField(i, 1, Mark.Black);
        }
        assertTrue(board.checkPlanes(Mark.Black));
        board.reset();
        
        //vertical row in xy-plane, z=1
        board.setField(0, 0, Mark.White);
        board.setField(0, 0, Mark.White);
        for (int i = 1; i <= Board.MAXFIELD; i++) {
            board.setField(0, i, Mark.Black);
            board.setField(0, i, Mark.White);
        }
        assertFalse(board.checkPlanes(Mark.Black));
        assertTrue(board.checkPlanes(Mark.White));
        board.reset();
        
        //check diagonal plane line (1,0,0 to 1,3,3)
        Mark m = Mark.Black;
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            //winning stone
            board.setField(1, i, m);
            for (int a = i + 1; a <= Board.MAXFIELD; a++) {
                //filling stones
                board.setField(1, a, m.other());
            }
        }
        assertTrue(board.checkPlanes(m));
        board.reset();
        
        //check diagonal plane line (0,1,0 to 3,1,3)
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            //winning stone
            board.setField(i, 1, m);
            for (int a = i + 1; a <= Board.MAXFIELD; a++) {
                //filling stones
                board.setField(a, 1, m.other());
            }
        }
        assertTrue(board.checkPlanes(m));
        board.reset();
        
        //check opposite diagonal plane line (1,3,0 to 1,0,3)
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            //winning stone
            board.setField(1, Board.MAXFIELD - i, m);
            for (int a = i + 1; a <= Board.MAXFIELD; a++) {
                //filling stones
                board.setField(1, Board.MAXFIELD - a, m.other());
            }
        }
        assertTrue(board.checkPlanes(m));
        System.out.println(board.toString());
        board.reset();
        
        //check opposite diagonal plane line (3,0,0 to 0,0,3)
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            //winning stone
            board.setField(Board.MAXFIELD - i, 0, m);
            for (int a = i + 1; a <= Board.MAXFIELD; a++) {
                //filling stones
                board.setField(Board.MAXFIELD - a, 0, m.other());
            }
        }
        assertTrue(board.checkPlanes(m));
        board.reset();
        
        //check cross line (0,0,0 to 3,3,0)
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            board.setField(i, i, m);
        }
        assertTrue(board.checkPlanes(m));
        board.reset();
        
        //check cross line (0,3,0 to 3,0,0)
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            board.setField(i, Board.MAXFIELD - i, m);
        }
        assertTrue(board.checkPlanes(m));
        board.reset();
    }
    
    @Test
    public void testisWinner() {
        Mark m = Mark.Black;
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            board.setField(i, i, m);
        }
        assertTrue(board.isWinner(m));
    }
    
    @Test
    public void testhasWinner() {
        Mark m = Mark.Black;
        assertFalse(board.hasWinner());
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            board.setField(i, 0, m);
        }
        assertTrue(board.hasWinner());
        for (int i = 0; i <= Board.MAXFIELD; i++) {
            board.setField(i, 1, m.other());
        }
        assertFalse(board.hasWinner());
        
    }
    
}
