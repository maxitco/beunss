package ss.week5;

public class ComputerPlayer extends Player {
    private Strategy strategy;
    
    public ComputerPlayer(Mark mark, Strategy strategyinput) {
        super(strategyinput.toString()+"-computer-"+mark.toString(),mark);
        this.strategy = strategyinput;
    }
    
    public ComputerPlayer(Mark mark) {
        this(mark, new NaiveStrategy());
    }
    @Override
    public int determineMove(Board board) {
        int move = this.strategy.determineMove(board, this.getMark());
        System.out.print(move);
        return move;
    }

}
