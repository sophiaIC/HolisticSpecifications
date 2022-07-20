contract Crowdsale {
    Escrow escrow;
    EscrowPublic escrow_p;
    uint256 closeTime;
    uint256 raised = 0;
    uint256 goal = 10000 * 10**18;

    function constructor() {
        escrow = new Escrow(this, 0x1234);
        escrow_p = new EscrowPublic(escrow);
        closeTime = now + 20 days;
    }

    function invest(address sender, uint256 value) payable {
        if(raised < goal && now <= closeTime){
            escrow.deposit(sender, value);
            raised += msg.value;
        }
    }

    function close() {
        if (now > closeTime || raised >= goal){
            if (raised >= goal) {
                escrow.close();
            } else {
                escrow.refund();
            }
        }
    }
}

/*
 * The private Escrow class
 */
contract Escrow {
    address owner, beneficiary;
    mapping (address => uint256) deposits;
    enum State (OPEN, SUCCESS, WITHDRAWN, REFUNDABLE, REFUNDED);
    State state = OPEN;

    constructor (address o, address b) {
        owner = o;
        beneficiary = b;
    }

    function close() {state = SUCCESS;}
    function setRefundable() {state = REFUNDABLE;}
    function setRefunded() {state = REFUNDED;}
    function setWithdrawn() {state = WITHDRAWN;}
    function deposit(address p, uint256 value) {
        deposits[p] = deposits[p] + value;
    }
    function withdraw(){
        if(state == SUCCESS){
            this.setWithdrawn();
            beneficiary.transfer(this.balance);
        }
    }
    function claimRefund(address p){
        if(state == REFUNDABLE){
            uint256 amount = this.deposits[p];
            this.setRefunded();
            this.deposits[p] = 0;
            p.call.value(amount)();
        }
    }
}

/*
 * The public interface of Escrow
 * the withdraw and refund methods of the escrow are exposed
 */
contract EscrowPublic{
    Escrow escrow;
    constructor (Escrow e){
        escrow = e;
    }
    function withdraw(){
        this.escrow.withdraw();
    }
    function claimRefund(address p){
        this.escrow.claimRefund(p)
    }
}
