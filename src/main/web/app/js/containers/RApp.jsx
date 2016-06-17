import { connect } from 'react-redux'
import App from '../components/App'

const mapStateToProps = (state) => (
  {
    showGiven: state.toShowEntryComplete,
    showProof: state.givenEntryComplete
  }
)

const RApp = connect(
  mapStateToProps
)(App)

export default RApp

