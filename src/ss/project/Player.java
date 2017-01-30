package ss.project;

public interface Player {
    public String getName();
    public Field determineMove(Board board, Mark m);
    
}
