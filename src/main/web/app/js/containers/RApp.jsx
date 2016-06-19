import { connect } from 'react-redux'
import App from '../components/App'

const mapStateToProps = (state) => (
  {
    showGiven: state.toShowEntryComplete,
    showProof: state.givenEntryComplete,
    mode: state.mode
  }
)

const RApp = connect(
  mapStateToProps
)(App)

export default RApp

