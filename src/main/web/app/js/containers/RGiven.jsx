import { connect } from 'react-redux'
import Given from '../components/Given'

const mapStateToProps = (state) => (
  {
    given: state.given.map(i => state.proof[i])
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    
  }
)

const RGiven = connect(
  mapStateToProps,
  mapDispatchToProps
)(Given)

export default RGiven

