package ss.project.view;

public interface View {
    public void start();
    public void run();    
    public void atStart();
    public void handleInput(String input);
    public void send(String inpt);
}
