import { connect } from 'react-redux'
import { PROOF_MODE } from '../constants'
import App from '../components/App'

const mapStateToProps = (state) => (
  {
    showGiven: state.mode == PROOF_MODE.DIRECT && state.toShowEntryComplete,
    showFnInput: state.mode == PROOF_MODE.INDUCTION && state.toShowEntryComplete,
    showDirectProof: state.mode == PROOF_MODE.DIRECT && state.givenEntryComplete,
    showInductiveProof: state.mode == PROOF_MODE.INDUCTION && state.givenEntryComplete
  }
)

const RApp = connect(
  mapStateToProps
)(App)

export default RApp

